-- Prove2me | solution 1 for MatchingLogic.Pattern.IsCaptureAvoidingSubst.denote
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:25:57.744394+00:00
-- url     : https://prove2.me/submissions/7ca6ef97-8733-4473-b011-348ad03e4b7e

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
public import Theorems.Thm_MatchingLogic_Model_denote_substVar_of_captureFree


set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}
open MatchingLogic.Pattern
namespace MatchingLogic.Pattern
namespace IsCaptureAvoidingSubst
theorem _root_.solution {x y : Nat} {p q : Pattern S Nat}
    (h : IsCaptureAvoidingSubst x y p q) (M : Model S)
    (rho : Nat → M.carrier) :
    M.denote rho q = M.denote (Function.update rho x (rho y)) p := by
  rcases h with ⟨p', halpha, hcf, rfl⟩
  rw [M.denote_substVar_of_captureFree rho hcf]
  exact halpha.denote_eq M _ |>.symm
end IsCaptureAvoidingSubst
end MatchingLogic.Pattern
