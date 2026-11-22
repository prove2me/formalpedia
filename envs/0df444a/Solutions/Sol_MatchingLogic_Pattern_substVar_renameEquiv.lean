-- Prove2me | solution 1 for MatchingLogic.Pattern.substVar_renameEquiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:43:19.280386+00:00
-- url     : https://prove2.me/submissions/4ba5a66f-5d23-495d-ad7f-0912de0d67f1

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Logic.Denumerable
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Renaming
public import Theorems.Thm_MatchingLogic_Pattern_substVar_rename_injective

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var Var' Var'' : Type}
open MatchingLogic.Pattern
namespace MatchingLogic.Pattern
theorem _root_.solution [DecidableEq Var] [DecidableEq Var']
    (e : Var ≃ Var') (x y : Var) (p : Pattern S Var) :
    (substVar x y p).rename e = substVar (e x) (e y) (p.rename e) :=
  substVar_rename_injective e e.injective x y p
end MatchingLogic.Pattern
