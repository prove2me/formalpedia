-- Prove2me | solution 1 for MatchingLogic.AppCtx.plug_renameEquiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:43:25.828348+00:00
-- url     : https://prove2.me/submissions/9b69c4a4-9ae0-41c8-ad1a-b7757823b491

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Logic.Denumerable
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Renaming
public import Theorems.Thm_MatchingLogic_AppCtx_plug_rename_injective

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var Var' Var'' : Type}
namespace MatchingLogic
namespace AppCtx
theorem _root_.solution
    (e : Var ≃ Var') (C : AppCtx S Var) (p : Pattern S Var) :
    (C.plug p).rename e = (C.rename e).plug (p.rename e) :=
  AppCtx.plug_rename_injective e C p
end AppCtx
end MatchingLogic
