(*$ open Ppxlib_cinaps_helpers $*)
open! Import
open Common
module E = Extension
module EC = Extension.Context
module A = Attribute
module AC = Attribute.Context

module Rule = struct
  module Attr_group_inline = struct
    type ('a, 'b, 'c) unpacked = {
      attribute : ('b, 'c) Attribute.t;
      expect : bool;
      expand :
        ctxt:Expansion_context.Deriver.t ->
        Asttypes.rec_flag ->
        'b list ->
        'c option list ->
        'a list;
    }

    type ('a, 'b) t = T : ('a, 'b, _) unpacked -> ('a, 'b) t

    let attr_name (T t) = Attribute.name t.attribute

    let split_normal_and_expect l =
      List.partition l ~f:(fun (T t) -> not t.expect)
  end

  module Attr_inline = struct
    type ('a, 'b, 'c) unpacked = {
      attribute : ('b, 'c) Attribute.t;
      expect : bool;
      expand : ctxt:Expansion_context.Deriver.t -> 'b -> 'c -> 'a list;
    }

    type ('a, 'b) t = T : ('a, 'b, _) unpacked -> ('a, 'b) t

    let attr_name (T t) = Attribute.name t.attribute

    let split_normal_and_expect l =
      List.partition l ~f:(fun (T t) -> not t.expect)
  end

  module Special_function = struct
    type t = {
      name : string;
      ident : Longident.t;
      expand : Parsetree.expression -> Parsetree.expression option;
    }
  end

  module Constant_kind = struct
    type t = Float | Integer
  end

  module Constant = struct
    type t = {
      suffix : char;
      kind : Constant_kind.t;
      expand : Location.t -> string -> Parsetree.expression;
    }
  end

  module Field = struct
    type 'a t =
      | Extension : Extension.t t
      | Special_function : Special_function.t t
      | Constant : Constant.t t
      | Attr_str_type_decl
          : (structure_item, type_declaration) Attr_group_inline.t t
      | Attr_sig_type_decl
          : (signature_item, type_declaration) Attr_group_inline.t t
      | Attr_str_module_type_decl
          : (structure_item, module_type_declaration) Attr_inline.t t
      | Attr_sig_module_type_decl
          : (signature_item, module_type_declaration) Attr_inline.t t
      | Attr_str_type_ext : (structure_item, type_extension) Attr_inline.t t
      | Attr_sig_type_ext : (signature_item, type_extension) Attr_inline.t t
      | Attr_str_exception : (structure_item, type_exception) Attr_inline.t t
      | Attr_sig_exception : (signature_item, type_exception) Attr_inline.t t

    type (_, _) equality = Eq : ('a, 'a) equality | Ne : (_, _) equality

    let eq : type a b. a t -> b t -> (a, b) equality =
     fun a b ->
      match (a, b) with
      | Extension, Extension -> Eq
      | Special_function, Special_function -> Eq
      | Constant, Constant -> Eq
      | Attr_str_type_decl, Attr_str_type_decl -> Eq
      | Attr_sig_type_decl, Attr_sig_type_decl -> Eq
      | Attr_str_type_ext, Attr_str_type_ext -> Eq
      | Attr_sig_type_ext, Attr_sig_type_ext -> Eq
      | Attr_str_exception, Attr_str_exception -> Eq
      | Attr_sig_exception, Attr_sig_exception -> Eq
      | Attr_str_module_type_decl, Attr_str_module_type_decl -> Eq
      | Attr_sig_module_type_decl, Attr_sig_module_type_decl -> Eq
      | _ -> Ne
  end

  type t = T : 'a Field.t * 'a -> t

  type ('a, 'b, 'c) attr_group_inline =
    ('b, 'c) Attribute.t ->
    (ctxt:Expansion_context.Deriver.t ->
    Asttypes.rec_flag ->
    'b list ->
    'c option list ->
    'a list) ->
    t

  type ('a, 'b, 'c) attr_inline =
    ('b, 'c) Attribute.t ->
    (ctxt:Expansion_context.Deriver.t -> 'b -> 'c -> 'a list) ->
    t

  let rec filter : type a. a Field.t -> t list -> a list =
   fun field l ->
    match l with
    | [] -> []
    | T (field', x) :: l -> (
        match Field.eq field field' with
        | Field.Eq -> x :: filter field l
        | Field.Ne -> filter field l)

  let extension ext = T (Extension, ext)

  let special_function id f =
    T (Special_function, { name = id; ident = Longident.parse id; expand = f })

  let constant kind suffix expand = T (Constant, { suffix; kind; expand })

  let attr_str_type_decl attribute expand =
    T (Attr_str_type_decl, T { attribute; expand; expect = false })

  let attr_sig_type_decl attribute expand =
    T (Attr_sig_type_decl, T { attribute; expand; expect = false })

  let attr_str_module_type_decl attribute expand =
    T (Attr_str_module_type_decl, T { attribute; expand; expect = false })

  let attr_sig_module_type_decl attribute expand =
    T (Attr_sig_module_type_decl, T { attribute; expand; expect = false })

  let attr_str_type_ext attribute expand =
    T (Attr_str_type_ext, T { attribute; expand; expect = false })

  let attr_sig_type_ext attribute expand =
    T (Attr_sig_type_ext, T { attribute; expand; expect = false })

  let attr_str_exception attribute expand =
    T (Attr_str_exception, T { attribute; expand; expect = false })

  let attr_sig_exception attribute expand =
    T (Attr_sig_exception, T { attribute; expand; expect = false })

  let attr_str_type_decl_expect attribute expand =
    T (Attr_str_type_decl, T { attribute; expand; expect = true })

  let attr_sig_type_decl_expect attribute expand =
    T (Attr_sig_type_decl, T { attribute; expand; expect = true })

  let attr_str_module_type_decl_expect attribute expand =
    T (Attr_str_module_type_decl, T { attribute; expand; expect = true })

  let attr_sig_module_type_decl_expect attribute expand =
    T (Attr_sig_module_type_decl, T { attribute; expand; expect = true })

  let attr_str_type_ext_expect attribute expand =
    T (Attr_str_type_ext, T { attribute; expand; expect = true })

  let attr_sig_type_ext_expect attribute expand =
    T (Attr_sig_type_ext, T { attribute; expand; expect = true })

  let attr_str_exception_expect attribute expand =
    T (Attr_str_exception, T { attribute; expand; expect = true })

  let attr_sig_exception_expect attribute expand =
    T (Attr_sig_exception, T { attribute; expand; expect = true })
end

module Generated_code_hook = struct
  type 'a single_or_many = Single of 'a | Many of 'a list

  type t = {
    f : 'a. 'a Extension.Context.t -> Location.t -> 'a single_or_many -> unit;
  }

  let nop = { f = (fun _ _ _ -> ()) }
  let replace t context loc x = t.f context loc x

  let insert_after t context (loc : Location.t) x =
    match x with
    | Many [] -> ()
    | _ -> t.f context { loc with loc_start = loc.loc_end } x
end

let rec map_node_rec context ts super_call loc base_ctxt x errors =
  let ctxt =
    Expansion_context.Extension.make ~extension_point_loc:loc ~base:base_ctxt ()
  in
  match EC.get_extension context x with
  | None -> super_call base_ctxt x errors
  | Some (ext, attrs) -> (
      match E.For_context.convert_res ts ~ctxt ext with
      | Error e -> (x, NonEmptyList.to_list e @ errors)
      | Ok converted -> (
          match converted with
          | None -> super_call base_ctxt x errors
          | Some x -> (
              match EC.merge_attributes_res context x attrs with
              | Ok x ->
                  map_node_rec context ts super_call loc base_ctxt x errors
              | Error e ->
                  map_node_rec context ts super_call loc base_ctxt x
                    (NonEmptyList.to_list e @ errors))))

let map_node context ts super_call loc base_ctxt x ~hook errors =
  let ctxt =
    Expansion_context.Extension.make ~extension_point_loc:loc ~base:base_ctxt ()
  in
  let res =
    match EC.get_extension context x with
    | None -> super_call base_ctxt x errors
    | Some (ext, attrs) -> (
        match E.For_context.convert_res ts ~ctxt ext with
        | Error e -> (x, NonEmptyList.to_list e @ errors)
        | Ok converted -> (
            match converted with
            | None -> super_call base_ctxt x errors
            | Some x ->
                let generated_code, errors =
                  map_node_rec context ts super_call loc base_ctxt
                    (EC.merge_attributes context x attrs)
                    errors
                in
                Generated_code_hook.replace hook context loc
                  (Single generated_code);
                (generated_code, errors)))
  in
  res

let rec map_nodes context ts super_call get_loc base_ctxt l ~hook
    ~in_generated_code errors =
  match l with
  | [] -> ([], errors)
  | x :: l -> (
      match EC.get_extension context x with
      | None ->
          (* These two lets force the evaluation order, so that errors are reported in the
             same order as they appear in the source file. *)
          let x, errors = super_call base_ctxt x errors in
          let l, errors =
            map_nodes context ts super_call get_loc base_ctxt l ~hook
              ~in_generated_code errors
          in
          (x :: l, errors)
      | Some (ext, attrs) -> (
          let extension_point_loc = get_loc x in
          let ctxt =
            Expansion_context.Extension.make ~extension_point_loc
              ~base:base_ctxt ()
          in
          match E.For_context.convert_inline_res ts ~ctxt ext with
          | Ok None ->
              let x, errors = super_call base_ctxt x errors in
              let l, errors =
                map_nodes context ts super_call get_loc base_ctxt l ~hook
                  ~in_generated_code errors
              in
              (x :: l, errors)
          | Ok (Some converted) ->
              let attributes_errors = attributes_errors attrs in
              if List.length attributes_errors = 0 then (
                let generated_code, errors =
                  map_nodes context ts super_call get_loc base_ctxt converted
                    ~hook ~in_generated_code:true errors
                in
                if not in_generated_code then
                  Generated_code_hook.replace hook context extension_point_loc
                    (Many generated_code);
                let nodes, errors =
                  map_nodes context ts super_call get_loc base_ctxt l ~hook
                    ~in_generated_code errors
                in
                (generated_code @ nodes, errors))
              else
                ( attributes_errors
                  |> List.map ~f:Location.Error.to_extension
                  |> List.map ~f:(EC.node_of_extension context ~x),
                  errors )
          | Error l ->
              ( l
                |> NonEmptyList.map ~f:Location.Error.to_extension
                |> NonEmptyList.map ~f:(EC.node_of_extension context ~x)
                |> NonEmptyList.to_list,
                errors )))

let map_nodes = map_nodes ~in_generated_code:false

let table_of_special_functions special_functions =
  match
    List.map special_functions
      ~f:(fun { Rule.Special_function.ident; expand; _ } -> (ident, expand))
    (* We expect the lookup to fail most of the time, by making the table big (and
       sparse), we make it more likely to fail quickly *)
    |> Hashtbl.of_alist ~size:(max 1024 (List.length special_functions * 2))
  with
  | Ok table -> table
  | Error ident ->
      Printf.ksprintf invalid_arg
        "Context_free.V1.map_top_down: %s present twice in list of special \
         functions"
        (List.find_map_exn special_functions ~f:(fun r ->
             if Poly.equal r.ident ident then Some r.name else None))

(* [get_group attr l] returns the list of the attributes for each
   node in [l].
   If [l] is empty or if none of the nodes in [l] have an attribute attached,
   [get_group] returns [None].
   If [l] is not empty and at least one of the nodes in [l] has an attribue
   attached, [get_group] returns the equivalent of
   [Some (List.map ~f:(Attribute.get attr) l)]. *)
let rec get_group attr l errors =
  match l with
  | [] -> (None, errors)
  | x :: l ->
      let group, errors = get_group attr l errors in
      let attr2 = Attribute.get_res attr x in
      let attr2, errors =
        match attr2 with
        | Ok attr2 -> (attr2, errors)
        | Error e -> (None, errors @ NonEmptyList.to_list e)
      in
      let res =
        match (attr2, group) with
        | None, None -> None
        | None, Some vals -> Some (None :: vals)
        | Some value, None -> Some (Some value :: List.map l ~f:(fun _ -> None))
        | Some value, Some vals -> Some (Some value :: vals)
      in
      (res, errors)

(* Same as [List.rev] then [List.concat] but expecting the input to be of length <= 2 *)
let rev_concat = function
  | [] -> []
  | [ x ] -> x
  | [ x; y ] -> y @ x
  | l -> List.concat (List.rev l)

let sort_attr_group_inline l =
  List.sort l ~cmp:(fun a b ->
      String.compare
        (Rule.Attr_group_inline.attr_name a)
        (Rule.Attr_group_inline.attr_name b))

let sort_attr_inline l =
  List.sort l ~cmp:(fun a b ->
      String.compare
        (Rule.Attr_inline.attr_name a)
        (Rule.Attr_inline.attr_name b))

let context_free_attribute_modification ~loc =
  ( Location.Error.createf ~loc
      "A context-free rule deleted or added attribues of a str/sig item",
    [] )

(* Returns the code generated by attribute handlers. We don't remove these attributes, as
   another pass might interpret them later. For instance both ppx_deriving and
   ppxlib_deriving interprets [@@deriving] attributes.

   This complexity is horrible, but in practice we don't care as [attrs] is always a list
   of one element; it only has [@@deriving].
*)
let handle_attr_group_inline attrs rf ~items ~expanded_items ~loc ~base_ctxt
    errors =
  List.fold_left attrs ~init:([], errors)
    ~f:(fun (acc, errors) (Rule.Attr_group_inline.T group) ->
      let g1, errors = get_group group.attribute items errors in
      let g2, errors = get_group group.attribute expanded_items errors in
      let res, errors =
        match (g1, g2) with
        | None, None -> (acc, errors)
        | None, Some _ | Some _, None ->
            ( acc,
              errors @ NonEmptyList.to_list
              @@ context_free_attribute_modification ~loc )
        | Some values, Some _ ->
            let ctxt =
              Expansion_context.Deriver.make ~derived_item_loc:loc
                ~inline:group.expect ~base:base_ctxt ()
            in
            let expect_items = group.expand ~ctxt rf expanded_items values in
            (expect_items :: acc, errors)
      in
      (res, errors))

let handle_attr_inline attrs ~item ~expanded_item ~loc ~base_ctxt errors =
  List.fold_left attrs ~init:([], errors)
    ~f:(fun (acc, errors) (Rule.Attr_inline.T a) ->
      let res_to_couple errors = function
        | Ok e -> (e, errors)
        | Error e -> (None, errors @ NonEmptyList.to_list e)
      in
      let g1, errors =
        Attribute.get_res a.attribute item |> res_to_couple errors
      in
      let g2, errors =
        Attribute.get_res a.attribute expanded_item |> res_to_couple errors
      in
      match (g1, g2) with
      | None, None -> (acc, errors)
      | None, Some _ | Some _, None ->
          ( acc,
            errors @ NonEmptyList.to_list
            @@ context_free_attribute_modification ~loc )
      | Some value, Some _ ->
          let ctxt =
            Expansion_context.Deriver.make ~derived_item_loc:loc
              ~inline:a.expect ~base:base_ctxt ()
          in
          let expect_items = a.expand ~ctxt expanded_item value in
          (expect_items :: acc, errors))

module Expect_mismatch_handler = struct
  type t = {
    f : 'a. 'a Attribute.Floating.Context.t -> Location.t -> 'a list -> unit;
  }

  let nop = { f = (fun _ _ _ -> ()) }
end

class map_top_down_with_errors
  ?(expect_mismatch_handler = Expect_mismatch_handler.nop)
  ?(generated_code_hook = Generated_code_hook.nop) rules =
  let hook = generated_code_hook in

  let special_functions =
    Rule.filter Special_function rules |> table_of_special_functions
  in
  let constants =
    Rule.filter Constant rules
    |> List.map ~f:(fun (c : Rule.Constant.t) -> ((c.suffix, c.kind), c.expand))
    |> Hashtbl.of_alist_exn
  in
  let extensions = Rule.filter Extension rules in
  let class_expr = E.filter_by_context EC.class_expr extensions
  and class_field = E.filter_by_context EC.class_field extensions
  and class_type = E.filter_by_context EC.class_type extensions
  and class_type_field = E.filter_by_context EC.class_type_field extensions
  and core_type = E.filter_by_context EC.core_type extensions
  and expression = E.filter_by_context EC.expression extensions
  and module_expr = E.filter_by_context EC.module_expr extensions
  and module_type = E.filter_by_context EC.module_type extensions
  and pattern = E.filter_by_context EC.pattern extensions
  and signature_item = E.filter_by_context EC.signature_item extensions
  and structure_item = E.filter_by_context EC.structure_item extensions
  and ppx_import = E.filter_by_context EC.Ppx_import extensions in

  let attr_str_type_decls, attr_str_type_decls_expect =
    Rule.filter Attr_str_type_decl rules
    |> sort_attr_group_inline |> Rule.Attr_group_inline.split_normal_and_expect
  in
  let attr_sig_type_decls, attr_sig_type_decls_expect =
    Rule.filter Attr_sig_type_decl rules
    |> sort_attr_group_inline |> Rule.Attr_group_inline.split_normal_and_expect
  in

  let attr_str_module_type_decls, attr_str_module_type_decls_expect =
    Rule.filter Attr_str_module_type_decl rules
    |> sort_attr_inline |> Rule.Attr_inline.split_normal_and_expect
  in
  let attr_sig_module_type_decls, attr_sig_module_type_decls_expect =
    Rule.filter Attr_sig_module_type_decl rules
    |> sort_attr_inline |> Rule.Attr_inline.split_normal_and_expect
  in

  let attr_str_type_exts, attr_str_type_exts_expect =
    Rule.filter Attr_str_type_ext rules
    |> sort_attr_inline |> Rule.Attr_inline.split_normal_and_expect
  in
  let attr_sig_type_exts, attr_sig_type_exts_expect =
    Rule.filter Attr_sig_type_ext rules
    |> sort_attr_inline |> Rule.Attr_inline.split_normal_and_expect
  in

  let attr_str_exceptions, attr_str_exceptions_expect =
    Rule.filter Attr_str_exception rules
    |> sort_attr_inline |> Rule.Attr_inline.split_normal_and_expect
  in
  let attr_sig_exceptions, attr_sig_exceptions_expect =
    Rule.filter Attr_sig_exception rules
    |> sort_attr_inline |> Rule.Attr_inline.split_normal_and_expect
  in

  let map_node = map_node ~hook in
  let map_nodes = map_nodes ~hook in

  object (self)
    inherit Ast_traverse.map_with_expansion_context_and_errors as super

    (* No point recursing into every location *)
    method! location _ x errors = (x, errors)

    method! core_type base_ctxt x errors =
      map_node EC.core_type core_type super#core_type x.ptyp_loc base_ctxt x
        errors

    method! pattern base_ctxt x errors =
      map_node EC.pattern pattern super#pattern x.ppat_loc base_ctxt x errors

    method! expression base_ctxt e errors =
      (* ignore (base_ctxt, e, errors); *)
      (* failwith "yo" *)
      let base_ctxt, e, errors =
        (* Make sure code-path attribute is applied before expanding. *)
        match Attribute.get_res Ast_traverse.enter_value e with
        | Error (err, errs) -> (base_ctxt, e, errors @ (err :: errs))
        | Ok None -> (base_ctxt, e, errors)
        | Ok (Some { loc; txt }) ->
            ( Expansion_context.Base.enter_value ~loc txt base_ctxt,
              Attribute.remove_seen Expression [ T Ast_traverse.enter_value ] e,
              errors )
      in
      let e, errors =
        match e.pexp_desc with
        | Pexp_extension _ ->
            map_node EC.expression expression
              (fun _ e errors -> (e, errors))
              e.pexp_loc base_ctxt e errors
        | _ -> (e, errors)
      in
      let expand_constant kind char text =
        match Hashtbl.find_opt constants (char, kind) with
        | None -> super#expression base_ctxt e errors
        | Some expand ->
            self#expression base_ctxt (expand e.pexp_loc text) errors
      in
      match e.pexp_desc with
      | Pexp_apply (({ pexp_desc = Pexp_ident id; _ } as func), args) -> (
          match Hashtbl.find_opt special_functions id.txt with
          | None ->
              self#pexp_apply_without_traversing_function base_ctxt e func args
                errors
          | Some pattern -> (
              match pattern e with
              | None ->
                  self#pexp_apply_without_traversing_function base_ctxt e func
                    args errors
              | Some e -> self#expression base_ctxt e errors))
      | Pexp_ident id -> (
          match Hashtbl.find_opt special_functions id.txt with
          | None -> super#expression base_ctxt e errors
          | Some pattern -> (
              match pattern e with
              | None -> super#expression base_ctxt e errors
              | Some e -> self#expression base_ctxt e errors))
      | Pexp_constant (Pconst_integer (s, Some c)) ->
          expand_constant Integer c s
      | Pexp_constant (Pconst_float (s, Some c)) -> expand_constant Float c s
      | _ -> super#expression base_ctxt e errors

    (* Pre-conditions:
       - e.pexp_desc = Pexp_apply(func, args)
       - func.pexp_desc = Pexp_ident _
    *)
    method private pexp_apply_without_traversing_function base_ctxt e func args
        errors =
      let { pexp_desc = _; pexp_loc; pexp_attributes; pexp_loc_stack } = e in
      let func, errors =
        let { pexp_desc; pexp_loc; pexp_attributes; pexp_loc_stack } = func in
        let pexp_attributes, errors =
          self#attributes base_ctxt pexp_attributes errors
        in
        ( {
            pexp_desc;
            pexp_loc (* location doesn't need to be traversed *);
            pexp_attributes;
            pexp_loc_stack;
          },
          errors )
      in
      let errors, args =
        List.fold_left_map args ~init:errors ~f:(fun errors (lab, exp) ->
            let exp, errors = self#expression base_ctxt exp errors in
            (errors, (lab, exp)))
      in
      let pexp_attributes, errors =
        self#attributes base_ctxt pexp_attributes errors
      in
      ( {
          pexp_loc;
          pexp_attributes;
          pexp_desc = Pexp_apply (func, args);
          pexp_loc_stack;
        },
        errors )

    method! class_type base_ctxt x errors =
      map_node EC.class_type class_type super#class_type x.pcty_loc base_ctxt x
        errors

    method! class_type_field base_ctxt x errors =
      map_node EC.class_type_field class_type_field super#class_type_field
        x.pctf_loc base_ctxt x errors

    method! class_expr base_ctxt x errors =
      map_node EC.class_expr class_expr super#class_expr x.pcl_loc base_ctxt x
        errors

    method! class_field base_ctxt x errors =
      map_node EC.class_field class_field super#class_field x.pcf_loc base_ctxt
        x errors

    method! module_type base_ctxt x errors =
      map_node EC.module_type module_type super#module_type x.pmty_loc base_ctxt
        x errors

    method! module_expr base_ctxt x errors =
      let base_ctxt, x, errors =
        (* Make sure code-path attribute is applied before expanding. *)
        match Attribute.get_res Ast_traverse.enter_module x with
        | Error (err, errs) -> (base_ctxt, x, errors @ (err :: errs))
        | Ok None -> (base_ctxt, x, errors)
        | Ok (Some { loc; txt }) ->
            ( Expansion_context.Base.enter_module ~loc txt base_ctxt,
              Attribute.remove_seen Module_expr
                [ T Ast_traverse.enter_module ]
                x,
              errors )
      in
      map_node EC.module_expr module_expr super#module_expr x.pmod_loc base_ctxt
        x errors

    method! structure_item base_ctxt x errors =
      map_node EC.structure_item structure_item super#structure_item x.pstr_loc
        base_ctxt x errors

    method! signature_item base_ctxt x errors =
      map_node EC.signature_item signature_item super#signature_item x.psig_loc
        base_ctxt x errors

    method! class_structure base_ctxt { pcstr_self; pcstr_fields } errors =
      let pcstr_self, errors = self#pattern base_ctxt pcstr_self errors in
      let pcstr_fields, errors =
        map_nodes EC.class_field class_field super#class_field
          (fun x -> x.pcf_loc)
          base_ctxt pcstr_fields errors
      in
      ({ pcstr_self; pcstr_fields }, errors)

    method! type_declaration base_ctxt x errors =
      map_node EC.Ppx_import ppx_import super#type_declaration x.ptype_loc
        base_ctxt x errors

    method! class_signature base_ctxt { pcsig_self; pcsig_fields } errors =
      let pcsig_self, errors = self#core_type base_ctxt pcsig_self errors in
      let pcsig_fields, errors =
        map_nodes EC.class_type_field class_type_field super#class_type_field
          (fun x -> x.pctf_loc)
          base_ctxt pcsig_fields errors
      in
      ({ pcsig_self; pcsig_fields }, errors)

    (* TODO: try to factorize #structure and #signature without meta-programming *)
    (*$*)
    method! structure base_ctxt st errors =
      let errors_to_items errors =
        errors
        |> List.map ~f:Location.Error.to_extension
        |> List.map ~f:(EC.node_of_extension EC.Structure_item)
      in
      let rec with_extra_items item ~extra_items ~expect_items ~rest
          ~in_generated_code =
        let extra_items =
          loop (rev_concat extra_items) ~in_generated_code:true
        in
        if not in_generated_code then
          Generated_code_hook.insert_after hook Structure_item item.pstr_loc
            (Many extra_items);
        let original_rest = rest in
        let errors =
          match expect_items with
          | [] -> errors
          | _ -> (
              let expected = rev_concat expect_items in
              let pos = item.pstr_loc.loc_end in
              match
                Code_matcher.match_structure_res original_rest ~pos ~expected
                  ~mismatch_handler:(fun loc repl ->
                    expect_mismatch_handler.f Structure_item loc repl)
              with
              | Error e -> NonEmptyList.to_list e
              | Ok () -> [])
        in
        item :: (errors_to_items errors @ extra_items)
      and handle_item item ~in_generated_code ~rest =
        let errors = [] in
        let loc = item.pstr_loc in
        let res, errors =
          match item.pstr_desc with
          | Pstr_extension (ext, attrs) -> (
              let extension_point_loc = item.pstr_loc in
              let ctxt =
                Expansion_context.Extension.make ~extension_point_loc
                  ~base:base_ctxt ()
              in
              match
                E.For_context.convert_inline_res structure_item ~ctxt ext
              with
              | Ok None ->
                  let item, errors =
                    super#structure_item base_ctxt item errors
                  in
                  ([ item ], errors)
              | Ok (Some items) ->
                  let errors = errors @ attributes_errors attrs in
                  let items = loop items ~in_generated_code:true in
                  if not in_generated_code then
                    Generated_code_hook.replace hook Structure_item
                      item.pstr_loc (Many items);
                  (items, errors)
              | Error err -> ([ item ], NonEmptyList.to_list err))
          | _ -> (
              let expanded_item, errors =
                super#structure_item base_ctxt item errors
              in
              match (item.pstr_desc, expanded_item.pstr_desc) with
              | Pstr_type (rf, tds), Pstr_type (exp_rf, exp_tds) ->
                  (* No context-free rule can rewrite rec flags atm, this
                     assert acts as a failsafe in case it ever changes *)
                  assert (Poly.(rf = exp_rf));
                  let extra_items, errors =
                    handle_attr_group_inline attr_str_type_decls rf ~items:tds
                      ~expanded_items:exp_tds ~loc ~base_ctxt errors
                  in
                  let expect_items, errors =
                    handle_attr_group_inline attr_str_type_decls_expect rf
                      ~items:tds ~expanded_items:exp_tds ~loc ~base_ctxt errors
                  in
                  ( with_extra_items expanded_item ~extra_items ~expect_items
                      ~rest ~in_generated_code,
                    errors )
              | Pstr_modtype mtd, Pstr_modtype exp_mtd ->
                  let extra_items, errors =
                    handle_attr_inline attr_str_module_type_decls ~item:mtd
                      ~expanded_item:exp_mtd ~loc ~base_ctxt errors
                  in
                  let expect_items, errors =
                    handle_attr_inline attr_str_module_type_decls_expect
                      ~item:mtd ~expanded_item:exp_mtd ~loc ~base_ctxt errors
                  in
                  ( with_extra_items expanded_item ~extra_items ~expect_items
                      ~rest ~in_generated_code,
                    errors )
              | Pstr_typext te, Pstr_typext exp_te ->
                  let extra_items, errors =
                    handle_attr_inline attr_str_type_exts ~item:te
                      ~expanded_item:exp_te ~loc ~base_ctxt errors
                  in
                  let expect_items, errors =
                    handle_attr_inline attr_str_type_exts_expect ~item:te
                      ~expanded_item:exp_te ~loc ~base_ctxt errors
                  in
                  ( with_extra_items expanded_item ~extra_items ~expect_items
                      ~rest ~in_generated_code,
                    errors )
              | Pstr_exception ec, Pstr_exception exp_ec ->
                  let extra_items, errors =
                    handle_attr_inline attr_str_exceptions ~item:ec
                      ~expanded_item:exp_ec ~loc ~base_ctxt errors
                  in
                  let expect_items, errors =
                    handle_attr_inline attr_str_exceptions_expect ~item:ec
                      ~expanded_item:exp_ec ~loc ~base_ctxt errors
                  in
                  ( with_extra_items expanded_item ~extra_items ~expect_items
                      ~rest ~in_generated_code,
                    errors )
              | _, _ -> ([ expanded_item ], errors))
        in
        errors_to_items errors @ res
      and loop st ~in_generated_code =
        match st with
        | [] -> []
        | item :: rest ->
            handle_item item ~rest ~in_generated_code
            @ loop rest ~in_generated_code
      in
      (errors_to_items errors @ loop st ~in_generated_code:false, [])

    (*$ str_to_sig _last_text_block *)
    method! signature base_ctxt sg errors =
      let errors_to_items errors =
        errors
        |> List.map ~f:Location.Error.to_extension
        |> List.map ~f:(EC.node_of_extension EC.Signature_item)
      in
      let rec with_extra_items item ~extra_items ~expect_items ~rest
          ~in_generated_code =
        let extra_items =
          loop (rev_concat extra_items) ~in_generated_code:true
        in
        if not in_generated_code then
          Generated_code_hook.insert_after hook Signature_item item.psig_loc
            (Many extra_items);
        let original_rest = rest in
        let errors =
          match expect_items with
          | [] -> errors
          | _ -> (
              let expected = rev_concat expect_items in
              let pos = item.psig_loc.loc_end in
              match
                Code_matcher.match_signature_res original_rest ~pos ~expected
                  ~mismatch_handler:(fun loc repl ->
                    expect_mismatch_handler.f Signature_item loc repl)
              with
              | Error e -> NonEmptyList.to_list e
              | Ok () -> [])
        in
        item :: (errors_to_items errors @ extra_items)
      and handle_item item ~in_generated_code ~rest =
        let errors = [] in
        let loc = item.psig_loc in
        let res, errors =
          match item.psig_desc with
          | Psig_extension (ext, attrs) -> (
              let extension_point_loc = item.psig_loc in
              let ctxt =
                Expansion_context.Extension.make ~extension_point_loc
                  ~base:base_ctxt ()
              in
              match
                E.For_context.convert_inline_res signature_item ~ctxt ext
              with
              | Ok None ->
                  let item, errors =
                    super#signature_item base_ctxt item errors
                  in
                  ([ item ], errors)
              | Ok (Some items) ->
                  let errors = errors @ attributes_errors attrs in
                  let items = loop items ~in_generated_code:true in
                  if not in_generated_code then
                    Generated_code_hook.replace hook Signature_item
                      item.psig_loc (Many items);
                  (items, errors)
              | Error err -> ([ item ], NonEmptyList.to_list err))
          | _ -> (
              let expanded_item, errors =
                super#signature_item base_ctxt item errors
              in
              match (item.psig_desc, expanded_item.psig_desc) with
              | Psig_type (rf, tds), Psig_type (exp_rf, exp_tds) ->
                  (* No context-free rule can rewrite rec flags atm, this
                     assert acts as a failsafe in case it ever changes *)
                  assert (Poly.(rf = exp_rf));
                  let extra_items, errors =
                    handle_attr_group_inline attr_sig_type_decls rf ~items:tds
                      ~expanded_items:exp_tds ~loc ~base_ctxt errors
                  in
                  let expect_items, errors =
                    handle_attr_group_inline attr_sig_type_decls_expect rf
                      ~items:tds ~expanded_items:exp_tds ~loc ~base_ctxt errors
                  in
                  ( with_extra_items expanded_item ~extra_items ~expect_items
                      ~rest ~in_generated_code,
                    errors )
              | Psig_modtype mtd, Psig_modtype exp_mtd ->
                  let extra_items, errors =
                    handle_attr_inline attr_sig_module_type_decls ~item:mtd
                      ~expanded_item:exp_mtd ~loc ~base_ctxt errors
                  in
                  let expect_items, errors =
                    handle_attr_inline attr_sig_module_type_decls_expect
                      ~item:mtd ~expanded_item:exp_mtd ~loc ~base_ctxt errors
                  in
                  ( with_extra_items expanded_item ~extra_items ~expect_items
                      ~rest ~in_generated_code,
                    errors )
              | Psig_typext te, Psig_typext exp_te ->
                  let extra_items, errors =
                    handle_attr_inline attr_sig_type_exts ~item:te
                      ~expanded_item:exp_te ~loc ~base_ctxt errors
                  in
                  let expect_items, errors =
                    handle_attr_inline attr_sig_type_exts_expect ~item:te
                      ~expanded_item:exp_te ~loc ~base_ctxt errors
                  in
                  ( with_extra_items expanded_item ~extra_items ~expect_items
                      ~rest ~in_generated_code,
                    errors )
              | Psig_exception ec, Psig_exception exp_ec ->
                  let extra_items, errors =
                    handle_attr_inline attr_sig_exceptions ~item:ec
                      ~expanded_item:exp_ec ~loc ~base_ctxt errors
                  in
                  let expect_items, errors =
                    handle_attr_inline attr_sig_exceptions_expect ~item:ec
                      ~expanded_item:exp_ec ~loc ~base_ctxt errors
                  in
                  ( with_extra_items expanded_item ~extra_items ~expect_items
                      ~rest ~in_generated_code,
                    errors )
              | _, _ -> ([ expanded_item ], errors))
        in
        errors_to_items errors @ res
      and loop sg ~in_generated_code =
        match sg with
        | [] -> []
        | item :: rest ->
            handle_item item ~rest ~in_generated_code
            @ loop rest ~in_generated_code
      in
      (errors_to_items errors @ loop sg ~in_generated_code:false, [])

    (*$*)
  end

class map_top_down ?(expect_mismatch_handler = Expect_mismatch_handler.nop)
  ?(generated_code_hook = Generated_code_hook.nop) rules =
  let ignore_errors = fst in
  let folder =
    new map_top_down_with_errors
      ~expect_mismatch_handler ~generated_code_hook rules
  in
  object
    inherit [Expansion_context.Base.t] Ast_traverse0.map_with_context
    method! location a x = folder#location a x [] |> ignore_errors

    method! core_type base_ctxt x =
      folder#core_type base_ctxt x [] |> ignore_errors

    method! pattern base_ctxt x = folder#pattern base_ctxt x [] |> ignore_errors

    method! expression base_ctxt e =
      folder#expression base_ctxt e [] |> ignore_errors

    (* Pre-conditions:
       - e.pexp_desc = Pexp_apply(func, args)
       - func.pexp_desc = Pexp_ident _
    *)
    method! class_type base_ctxt x =
      folder#class_type base_ctxt x [] |> ignore_errors

    method! class_type_field base_ctxt x =
      folder#class_type_field base_ctxt x [] |> ignore_errors

    method! class_expr base_ctxt x =
      folder#class_expr base_ctxt x [] |> ignore_errors

    method! class_field base_ctxt x =
      folder#class_field base_ctxt x [] |> ignore_errors

    method! module_type base_ctxt x =
      folder#module_type base_ctxt x [] |> ignore_errors

    method! module_expr base_ctxt x =
      folder#module_expr base_ctxt x [] |> ignore_errors

    method! structure_item base_ctxt x =
      folder#structure_item base_ctxt x [] |> ignore_errors

    method! signature_item base_ctxt x =
      folder#signature_item base_ctxt x [] |> ignore_errors

    method! class_structure base_ctxt { pcstr_self; pcstr_fields } =
      folder#class_structure base_ctxt { pcstr_self; pcstr_fields } []
      |> ignore_errors

    method! type_declaration base_ctxt x =
      folder#type_declaration base_ctxt x [] |> ignore_errors

    method! class_signature base_ctxt { pcsig_self; pcsig_fields } =
      folder#class_signature base_ctxt { pcsig_self; pcsig_fields } []
      |> ignore_errors

    (*$*)
    method! structure base_ctxt st =
      folder#structure base_ctxt st [] |> ignore_errors

    (*$ str_to_sig _last_text_block *)
    method! signature base_ctxt sg =
      folder#signature base_ctxt sg [] |> ignore_errors

    (*$*)
  end
