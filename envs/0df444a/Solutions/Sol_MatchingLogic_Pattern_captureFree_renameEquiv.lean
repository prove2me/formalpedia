-- Prove2me | solution 1 for MatchingLogic.Pattern.captureFree_renameEquiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:43:19.658819+00:00
-- url     : https://prove2.me/submissions/8eaec3db-2981-4be2-afbc-bb655bdfec0c

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Logic.Denumerable
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Renaming
public import Theorems.Thm_MatchingLogic_Pattern_captureFree_rename_injective

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var Var' Var'' : Type}
open MatchingLogic.Pattern
namespace MatchingLogic.Pattern
theorem _root_.solution
    (e : Var ≃ Var') {x y : Var} {p : Pattern S Var}
    (h : CaptureFree x y p) :
    CaptureFree (e x) (e y) (p.rename e) :=
  captureFree_rename_injective e e.injective h
end MatchingLogic.Pattern
