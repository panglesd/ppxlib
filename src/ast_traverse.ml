open! Import
include Ast_traverse0

let module_name = function None -> "_" | Some name -> name
let enter name path = if String.is_empty path then name else path ^ "." ^ name
let enter_opt name_opt path = enter (module_name name_opt) path

class map_with_path =
  object
    inherit [string] map_with_context as super

    (* WAS:
       method! structure_item_desc path x =
       match x with
       | Pstr_module mb -> super#structure_item_desc (enter mb.pmb_name.txt path) x
       | _ -> super#structure_item_desc path x

       Overriding [module_binding] seems to be OK because it does not catch
       local module bindings because at the moment the parsetree doesn't make
       use of [module_binding] for local modules, but that might change in the
       future, so this might be something to keep in mind.

       The following:

           module A = struct .. end
           module A = struct .. end

       is disallowed, but

           let _ = .. let module A = struct .. end in ..
           module A = struct .. end
           let _ = .. let module A = struct .. end in ..

       isn't, and the "path" constructed here would be able to differentiate
       between them. *)
    method! module_binding path mb =
      super#module_binding (enter_opt mb.pmb_name.txt path) mb

    method! module_declaration path md =
      super#module_declaration (enter_opt md.pmd_name.txt path) md

    method! module_type_declaration path mtd =
      super#module_type_declaration (enter mtd.pmtd_name.txt path) mtd
  end

let var_names_of =
  object
    inherit [string list] fold as super

    method! pattern p acc =
      let acc = super#pattern p acc in
      match p.ppat_desc with Ppat_var { txt; _ } -> txt :: acc | _ -> acc
  end

let ec_enter_module_opt ~loc name_opt ctxt =
  Expansion_context.Base.enter_module ~loc (module_name name_opt) ctxt

let enter_value =
  Attribute.declare "ppxlib.enter_value" Expression
    Ast_pattern.(single_expr_payload (pexp_ident (lident __')))
    Fn.id

let enter_module =
  Attribute.declare "ppxlib.enter_module" Module_expr
    Ast_pattern.(single_expr_payload (pexp_construct (lident __') none))
    Fn.id

let do_not_enter_value_binding =
  Attribute.declare "ppxlib.do_not_enter_value" Value_binding
    Ast_pattern.(pstr nil)
    ()

let do_not_enter_value_description =
  Attribute.declare "ppxlib.do_not_enter_value" Value_description
    Ast_pattern.(pstr nil)
    ()

let do_not_enter_module_binding =
  Attribute.declare "ppxlib.do_not_enter_module" Module_binding
    Ast_pattern.(pstr nil)
    ()

let do_not_enter_module_declaration =
  Attribute.declare "ppxlib.do_not_enter_module" Module_declaration
    Ast_pattern.(pstr nil)
    ()

let do_not_enter_module_type_declaration =
  Attribute.declare "ppxlib.do_not_enter_module" Module_type_declaration
    Ast_pattern.(pstr nil)
    ()

let do_not_enter_let_module =
  Attribute.declare "ppxlib.do_not_enter_module" Expression
    Ast_pattern.(pstr nil)
    ()

class map_with_expansion_context_and_errors =
  object (self)
    inherit
      [Expansion_context.Base.t, Location.Error.t list] fold_map_with_context as super

    method! expression ctxt
        ({ pexp_desc; pexp_loc; pexp_loc_stack; pexp_attributes } as expr)
        errors =
      let ctxt =
        match Attribute.get enter_value expr with
        | None -> ctxt
        | Some { loc; txt } -> Expansion_context.Base.enter_value ~loc txt ctxt
      in
      let ctxt = Expansion_context.Base.enter_expr ctxt in
      let pexp_desc, errors =
        match pexp_desc with
        | Pexp_letmodule (name, module_expr, body) ->
            let name, errors =
              self#loc (self#option self#string) ctxt name errors
            in
            let module_expr, errors =
              let ctxt =
                match Attribute.get do_not_enter_let_module expr with
                | Some () -> ctxt
                | None ->
                    ec_enter_module_opt ~loc:module_expr.pmod_loc name.txt ctxt
              in
              self#module_expr ctxt module_expr errors
            in
            let body, errors = self#expression ctxt body errors in
            (Pexp_letmodule (name, module_expr, body), errors)
        | _ -> self#expression_desc ctxt pexp_desc errors
      in
      let pexp_loc, errors = self#location ctxt pexp_loc errors in
      let pexp_loc_stack, errors =
        self#list self#location ctxt pexp_loc_stack errors
      in
      let pexp_attributes, errors =
        self#attributes ctxt pexp_attributes errors
      in
      ({ pexp_desc; pexp_loc; pexp_loc_stack; pexp_attributes }, errors)

    method! module_expr ctxt me errors =
      let ctxt, errors =
        match Attribute.get_res enter_module me with
        | Error (err, l_err) -> (ctxt, (err :: l_err) @ errors)
        | Ok None -> (ctxt, errors)
        | Ok (Some { loc; txt }) ->
            (Expansion_context.Base.enter_module ~loc txt ctxt, errors)
      in
      super#module_expr ctxt me errors

    method! module_binding ctxt mb errors =
      let ctxt, errors =
        match Attribute.get_res do_not_enter_module_binding mb with
        | Error (err, l_err) ->
            ( ec_enter_module_opt ~loc:mb.pmb_loc mb.pmb_name.txt ctxt,
              (err :: l_err) @ errors )
        | Ok (Some ()) -> (ctxt, errors)
        | Ok None ->
            (ec_enter_module_opt ~loc:mb.pmb_loc mb.pmb_name.txt ctxt, errors)
      in
      super#module_binding ctxt mb errors

    method! module_declaration ctxt md errors =
      let ctxt, errors =
        match Attribute.get_res do_not_enter_module_declaration md with
        | Error (err, l_err) ->
            ( ec_enter_module_opt ~loc:md.pmd_loc md.pmd_name.txt ctxt,
              (err :: l_err) @ errors )
        | Ok (Some ()) -> (ctxt, errors)
        | Ok None ->
            (ec_enter_module_opt ~loc:md.pmd_loc md.pmd_name.txt ctxt, errors)
      in
      super#module_declaration ctxt md errors

    method! module_type_declaration ctxt mtd errors =
      let ctxt, errors =
        match Attribute.get_res do_not_enter_module_type_declaration mtd with
        | Error (err, l_err) ->
            ( Expansion_context.Base.enter_module ~loc:mtd.pmtd_loc
                mtd.pmtd_name.txt ctxt,
              (err :: l_err) @ errors )
        | Ok (Some ()) -> (ctxt, errors)
        | Ok None ->
            ( Expansion_context.Base.enter_module ~loc:mtd.pmtd_loc
                mtd.pmtd_name.txt ctxt,
              errors )
      in
      super#module_type_declaration ctxt mtd errors

    method! value_description ctxt vd errors =
      let ctxt, errors =
        match Attribute.get_res do_not_enter_value_description vd with
        | Error (err, l_err) ->
            ( Expansion_context.Base.enter_value ~loc:vd.pval_loc
                vd.pval_name.txt ctxt,
              (err :: l_err) @ errors )
        | Ok (Some ()) -> (ctxt, errors)
        | Ok None ->
            ( Expansion_context.Base.enter_value ~loc:vd.pval_loc
                vd.pval_name.txt ctxt,
              errors )
      in
      super#value_description ctxt vd errors

    method! value_binding ctxt
        ({ pvb_pat; pvb_expr; pvb_attributes; pvb_loc } as vb) errors =
      match Attribute.get_res do_not_enter_value_binding vb with
      | Error (err, l_err) ->
          let in_binding_ctxt =
            match var_names_of#pattern pvb_pat [] with
            | [] | _ :: _ :: _ -> ctxt
            | [ var_name ] ->
                Expansion_context.Base.enter_value ~loc:pvb_loc var_name ctxt
          in
          let pvb_pat, errors = self#pattern ctxt pvb_pat errors in
          let pvb_expr, errors =
            self#expression in_binding_ctxt pvb_expr errors
          in
          let pvb_attributes, errors =
            self#attributes in_binding_ctxt pvb_attributes errors
          in
          let pvb_loc, errors = self#location ctxt pvb_loc errors in
          ( { pvb_pat; pvb_expr; pvb_attributes; pvb_loc },
            (err :: l_err) @ errors )
      | Ok (Some ()) -> super#value_binding ctxt vb errors
      | Ok None ->
          let in_binding_ctxt =
            match var_names_of#pattern pvb_pat [] with
            | [] | _ :: _ :: _ -> ctxt
            | [ var_name ] ->
                Expansion_context.Base.enter_value ~loc:pvb_loc var_name ctxt
          in
          let pvb_pat, errors = self#pattern ctxt pvb_pat errors in
          let pvb_expr, errors =
            self#expression in_binding_ctxt pvb_expr errors
          in
          let pvb_attributes, errors =
            self#attributes in_binding_ctxt pvb_attributes errors
          in
          let pvb_loc, errors = self#location ctxt pvb_loc errors in
          ({ pvb_pat; pvb_expr; pvb_attributes; pvb_loc }, errors)
  end

class map_with_expansion_context =
  let folder = new map_with_expansion_context_and_errors in
  object
    inherit [Expansion_context.Base.t] map_with_context
    method! expression ctxt expr = folder#expression ctxt expr [] |> fst
    method! module_expr ctxt me = folder#module_expr ctxt me [] |> fst
    method! module_binding ctxt mb = folder#module_binding ctxt mb [] |> fst

    method! module_declaration ctxt md =
      folder#module_declaration ctxt md [] |> fst

    method! module_type_declaration ctxt mtd =
      folder#module_type_declaration ctxt mtd [] |> fst

    method! value_description ctxt vd =
      folder#value_description ctxt vd [] |> fst

    method! value_binding ctxt vb = folder#value_binding ctxt vb [] |> fst
  end

class sexp_of =
  object
    inherit [Sexp.t] Ast.lift
    method int = sexp_of_int
    method string = sexp_of_string
    method bool = sexp_of_bool
    method char = sexp_of_char
    method float = sexp_of_float
    method int32 = sexp_of_int32
    method int64 = sexp_of_int64
    method nativeint = sexp_of_nativeint
    method unit = sexp_of_unit
    method option = sexp_of_option
    method list = sexp_of_list
    method array : 'a. ('a -> Sexp.t) -> 'a array -> Sexp.t = sexp_of_array
    method other : 'a. 'a -> Sexp.t = fun _ -> Sexp.Atom "_"

    method record fields =
      List
        (List.map fields ~f:(fun (label, sexp) ->
             Sexp.List [ Atom label; sexp ]))

    method constr tag args =
      match args with [] -> Atom tag | _ -> List (Atom tag :: args)

    method tuple l = List l
  end

let sexp_of = new sexp_of
