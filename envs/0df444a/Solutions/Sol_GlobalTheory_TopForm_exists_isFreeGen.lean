-- Prove2me | solution 1 for GlobalTheory.TopForm.exists_isFreeGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:34:41.865641+00:00
-- url     : https://prove2.me/submissions/cb62255a-4cab-44ba-80fb-8cb2a55b780c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsAlgHomOfIsBaseChange
import Theorems.Thm_P2M_GlobalTheory_TopForm_isFreeGen__Multi_52fc91f67394

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.TopForm
variable {k A B C : Type*} [CommRing k] [CommRing A] [CommRing B] [CommRing C]
variable {D : ℕ}
variable {α : k →+* A} {β : k →+* B} {γ : k →+* C}
namespace GlobalTheory.TopForm
theorem _root_.solution (h : α.IsStandardSmoothOfRelativeDimension D) :
    ∃ ω : Forms α D, IsFreeGen A ω := by
  letI := α.toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension D k A := h
  cases subsingleton_or_nontrivial A with
  | inl _ =>
    haveI := Module.subsingleton A (Forms α D)
    exact ⟨0, fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩
  | inr _ =>
    haveI := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth D (R := k) (S := A)
    haveI : Module.Free A (Omega α) := inferInstanceAs (Module.Free A Ω[A⁄k])
    haveI : Module.Finite A (Omega α) := inferInstanceAs (Module.Finite A Ω[A⁄k])
    have hr : Module.finrank A (Omega α) = D := Module.finrank_eq_of_rank_eq
      (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := k) (S := A) D)
    exact ⟨_, isFreeGen_ιMulti (Module.finBasisOfFinrankEq A (Omega α) hr)⟩
end GlobalTheory.TopForm
