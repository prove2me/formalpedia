-- Prove2me | solution 1 for MatchingLogic.Model.denote_captureAvoidingSubst
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:28:23.657202+00:00
-- url     : https://prove2.me/submissions/5f6bc143-77a8-42ba-8bbd-1fc30964e11a

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Fresh
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_Soundness
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CaptureAvoiding
public import Theorems.Thm_MatchingLogic_Pattern_AlphaEq_symm
public import Theorems.Thm_MatchingLogic_Pattern_AlphaEq_denote_eq
public import Theorems.Thm_MatchingLogic_Pattern_avoidBinder_avoids
public import Theorems.Thm_MatchingLogic_Pattern_AvoidsBinder_captureFree
public import Theorems.Thm_MatchingLogic_Pattern_avoidBinder_alphaEq
public import Theorems.Thm_MatchingLogic_Model_denote_substVar_of_captureFree


set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}
namespace MatchingLogic
namespace Model
theorem _root_.solution (M : Model S)
    (rho : Nat → M.carrier) (x y : Nat) (p : Pattern S Nat) :
    M.denote rho (Pattern.captureAvoidingSubst x y p) =
      M.denote (Function.update rho x (rho y)) p := by
  rw [Pattern.captureAvoidingSubst,
    M.denote_substVar_of_captureFree rho
      (Pattern.avoidBinder_avoids y p).captureFree]
  exact (Pattern.avoidBinder_alphaEq y p).denote_eq M _ |>.symm
end Model
end MatchingLogic
