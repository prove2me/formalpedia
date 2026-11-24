-- Prove2me | solution 1 for GlobalTheory.exists_short_family_adapted
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:06:06.081553+00:00
-- url     : https://prove2.me/submissions/edfde30b-9640-4ce0-a659-43e3b91d4279

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsLinearIndependentSqrtEqSuccMinQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsShortBasisAdaptedOfSubsetSpan
import Theorems.Thm_GlobalTheory_exists_short_generator_inf_span_insert

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Submodule
open scoped InnerProductSpace
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
namespace GlobalTheory
theorem _root_.solution (L : Submodule ℤ E) [DiscreteTopology L] {n : ℕ}
    {v : Fin n → E} (hv : LinearIndependent ℝ v) (hL : ∀ i, v i ∈ L) :
    ∃ b : Fin n → E, LinearIndependent ℝ b ∧
      (∀ s : ℕ, span ℤ (b '' {i : Fin n | (i : ℕ) < s}) =
        L ⊓ (span ℝ (v '' {i : Fin n | (i : ℕ) < s})).restrictScalars ℤ) ∧
      ∀ i, ‖b i‖ ^ 2 ≤ ‖v i‖ ^ 2 + (1 / 4) * ∑ j ∈ Finset.Iio i, ‖v j‖ ^ 2 := by
  choose b hb hbn using fun i : Fin n => exists_short_generator_inf_span_insert L v
    (Finset.Iio i) (fun j _ => hL j) (hL i) (hv.notMem_span_image (by simp))
  have key : ∀ s : ℕ, span ℤ (b '' {i : Fin n | (i : ℕ) < s}) =
      L ⊓ (span ℝ (v '' {i : Fin n | (i : ℕ) < s})).restrictScalars ℤ := by
    intro s
    induction s with
    | zero => simp
    | succ s ih =>
      by_cases hs : s < n
      · have h1 : {i : Fin n | (i : ℕ) < s + 1} = insert ⟨s, hs⟩ {i : Fin n | (i : ℕ) < s} := by
          ext i; simp [Fin.ext_iff]; omega
        have h2 : ((Finset.Iio (⟨s, hs⟩ : Fin n) : Finset (Fin n)) : Set (Fin n)) =
            {i : Fin n | (i : ℕ) < s} := by
          ext i; simp [Fin.lt_def]
        have h3 := hb ⟨s, hs⟩
        rw [h2] at h3
        rw [h1, Set.image_insert_eq, Set.image_insert_eq, h3, span_insert, ih]
      · have h1 : {i : Fin n | (i : ℕ) < s + 1} = {i : Fin n | (i : ℕ) < s} := by
          ext i; have := i.2; simp; omega
        rw [h1, ih]
  refine ⟨b, ?_, key, hbn⟩
  have hu : {i : Fin n | (i : ℕ) < n} = Set.univ := by ext i; simp
  have h := key n
  rw [hu, Set.image_univ, Set.image_univ] at h
  have hsp : span ℝ (Set.range b) = span ℝ (Set.range v) := by
    refine le_antisymm (span_le.2 fun x hx => ?_) (span_le.2 ?_)
    · exact (h.le (subset_span hx)).2
    · rintro _ ⟨i, rfl⟩
      exact span_subset_span ℤ ℝ _ (h.ge ⟨hL i, subset_span ⟨i, rfl⟩⟩)
  rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, hsp, finrank_span_eq_card hv]
end GlobalTheory
