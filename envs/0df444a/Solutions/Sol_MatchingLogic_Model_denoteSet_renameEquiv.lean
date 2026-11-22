-- Prove2me | solution 1 for MatchingLogic.Model.denoteSet_renameEquiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:43:55.155912+00:00
-- url     : https://prove2.me/submissions/332f6b25-1352-4f3e-a49d-4196ab42da26

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Logic.Denumerable
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Renaming
public import Theorems.Thm_MatchingLogic_Model_denoteSet_renameInjective

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var Var' Var'' : Type}
namespace MatchingLogic
namespace Model
theorem _root_.solution [DecidableEq Var] [DecidableEq Var']
    (M : Model S) (e : Var ≃ Var') (rho : Var' → M.carrier)
    (Delta : Set (Pattern S Var)) :
    M.denoteSet rho (Pattern.rename e '' Delta) = M.denoteSet (rho ∘ e) Delta :=
  M.denoteSet_renameInjective e e.injective rho Delta
end Model
end MatchingLogic
