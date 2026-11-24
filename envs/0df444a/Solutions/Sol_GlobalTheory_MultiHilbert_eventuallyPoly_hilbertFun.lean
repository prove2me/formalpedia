-- Prove2me | solution 1 for GlobalTheory.MultiHilbert.eventuallyPoly_hilbertFun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:53:00.144201+00:00
-- url     : https://prove2.me/submissions/e5e71ff4-efd4-4b95-af20-1039ac27ba5f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsMultigradedHilbertPoly
import Theorems.Thm_GlobalTheory_MultiHilbert_EventuallyPoly_add
import Theorems.Thm_GlobalTheory_MultiHilbert_EventuallyPoly_shift_add
import Theorems.Thm_GlobalTheory_MultiHilbert_EventuallyPoly_of_shift_add
import Theorems.Thm_GlobalTheory_MultiHilbert_EventuallyPoly_of_differences
import Theorems.Thm_GlobalTheory_MultiHilbert_le_colonX
import Theorems.Thm_GlobalTheory_MultiHilbert_component_mem_colonX
import Theorems.Thm_GlobalTheory_MultiHilbert_component_mem_sup
import Theorems.Thm_GlobalTheory_MultiHilbert_colourPiece_le
import Theorems.Thm_GlobalTheory_MultiHilbert_hilbertFun_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MultiHilbert
open MvPolynomial
namespace GlobalTheory.MultiHilbert
theorem _root_.solution {K σ : Type} [Field K] [Finite σ] {r : ℕ} (col : σ → Fin r)
    (I : Ideal (MvPolynomial σ K))
    (hI : ∀ F ∈ I, ∀ n : Fin r → ℕ, weightedHomogeneousComponent
      (fun i => (Pi.single (col i) 1 : Fin r → ℕ)) n F ∈ I) :
    EventuallyPoly (hilbertFun col I) := by
  induction I using IsNoetherian.induction with
  | hgt I ih =>
    by_cases h0 : ∃ k, ∀ i, col i = k → X i ∈ I
    · obtain ⟨k, hk⟩ := h0
      refine ⟨0, 1, fun n hn => ?_⟩
      unfold hilbertFun
      rw [inf_eq_left.2 (colourPiece_le col k hk n (hn k))]
      simp
    push Not at h0
    have hsup : ∀ i, X i ∉ I → EventuallyPoly (hilbertFun col (I ⊔ Ideal.span {X i})) := by
      intro i hi
      refine ih _ (lt_of_le_of_ne le_sup_left fun h => hi ?_) (component_mem_sup _ hI i)
      rw [h]
      exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
    by_cases h1 : ∃ i, X i ∉ I ∧ colonX I i ≠ I
    · obtain ⟨i, hi, hne⟩ := h1
      have h2 := ih _ (lt_of_le_of_ne (le_colonX I i) hne.symm) (component_mem_colonX _ hI i)
      refine EventuallyPoly.of_shift_add (Pi.single (col i) 1) ?_
      simp only [hilbertFun_add col hI i]
      exact h2.add ((hsup i hi).shift_add _)
    push Not at h1
    refine EventuallyPoly.of_differences fun k => ?_
    obtain ⟨i, rfl, hi⟩ := h0 k
    simp only [hilbertFun_add col hI i, h1 i hi, add_sub_cancel_left]
    exact (hsup i hi).shift_add _
end GlobalTheory.MultiHilbert
