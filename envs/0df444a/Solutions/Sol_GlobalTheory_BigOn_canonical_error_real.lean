-- Prove2me | solution 1 for GlobalTheory.BigOn.canonical_error_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:37:38.637731+00:00
-- url     : https://prove2.me/submissions/10edf4bf-eb33-4fa8-947a-bc825e5bc20d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ExampleSatisfiesConditionsAtFive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OnOfOnWithCanonical

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.L2.Indef Formalism.L2.Indef.Tree
open GlobalTheory GlobalTheory.BigOn
namespace GlobalTheory.BigOn
theorem _root_.solution {ι J : Type} [Fintype J] (T : Finset ι) (I F err err0 J0 : ι → J → ℝ)
    (e c l : ι → ℝ) (D E E' : ℝ) (hD : 0 < D) (he : ∀ w, 0 < e w) (hl : ∀ w, 0 ≤ l w) (hE : 2 * E ≤ E')
    (hJ : ∀ w ∈ T, ∀ j, 0 ≤ J0 w j)
    (h0 : ∀ w j, err0 w j =
      max 0 ((∑ j', I w j') / D - ∑ j', 2 * (e w * F w j') - c w) / (e w * (Fintype.card J : ℝ)))
    (h1 : ∀ w ∈ T, ∑ j, I w j ≤ (∑ j, (2 * (e w * F w j) + e w * err w j) + c w) * D)
    (h2 : ∀ w ∈ T, ∀ j, 0 ≤ err w j)
    (h3 : ∀ j, ∑ w ∈ T, l w * (e w * err w j + e w * J0 w j) ≤ E) :
    (∀ w ∈ T, ∑ j, I w j ≤ (∑ j, (2 * (e w * F w j) + e w * err0 w j) + c w) * D) ∧
    (∀ w ∈ T, ∀ j, 0 ≤ err0 w j) ∧
    ∀ j, ∑ w ∈ T, l w * (e w * err0 w j + e w * J0 w j) ≤ E' := by
  refine ⟨fun w hw => ?_, fun w _ j => ?_, fun j => ?_⟩
  · rcases isEmpty_or_nonempty J with hJe | hJn
    · simpa using h1 w hw
    · have hn : (0 : ℝ) < (Fintype.card J : ℝ) := by exact_mod_cast Fintype.card_pos
      have hew := he w
      have hs : ∑ j, e w * err0 w j =
          max 0 ((∑ j', I w j') / D - ∑ j', 2 * (e w * F w j') - c w) := by
        simp only [h0, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp
      rw [Finset.sum_add_distrib, hs, ← div_le_iff₀ hD]
      have := le_max_right 0 ((∑ j', I w j') / D - ∑ j', 2 * (e w * F w j') - c w)
      linarith
  · rw [h0]
    exact div_nonneg (le_max_left _ _) (mul_nonneg (he w).le (Nat.cast_nonneg _))
  · have hn : (0 : ℝ) < (Fintype.card J : ℝ) := by
      exact_mod_cast (Fintype.card_pos_iff.mpr ⟨j⟩)
    have hA : ∀ w ∈ T, (Fintype.card J : ℝ) * (l w * (e w * err0 w j)) ≤ ∑ j', l w * (e w * err w j') := by
      intro w hw
      have hew := he w
      have hs : (Fintype.card J : ℝ) * (l w * (e w * err0 w j)) =
          l w * max 0 ((∑ j', I w j') / D - ∑ j', 2 * (e w * F w j') - c w) := by
        rw [h0]; field_simp
      rw [hs, ← Finset.mul_sum _ _ (l w)]
      refine mul_le_mul_of_nonneg_left (max_le ?_ ?_) (hl w)
      · exact Finset.sum_nonneg fun j' _ => mul_nonneg hew.le (h2 w hw j')
      · have h := h1 w hw
        rw [Finset.sum_add_distrib, ← div_le_iff₀ hD] at h
        linarith
    have hB : ∀ j', ∑ w ∈ T, l w * (e w * err w j') ≤ E := fun j' =>
      le_trans (Finset.sum_le_sum fun w hw => mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (mul_nonneg (he w).le (hJ w hw j'))) (hl w)) (h3 j')
    have hC : ∑ w ∈ T, l w * (e w * J0 w j) ≤ E :=
      le_trans (Finset.sum_le_sum fun w hw => mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left (mul_nonneg (he w).le (h2 w hw j))) (hl w)) (h3 j)
    have hF : (Fintype.card J : ℝ) * ∑ w ∈ T, l w * (e w * err0 w j) ≤ (Fintype.card J : ℝ) * E := by
      rw [Finset.mul_sum]
      refine le_trans (Finset.sum_le_sum hA) ?_
      rw [Finset.sum_comm]
      refine le_trans (Finset.sum_le_sum fun j' _ => hB j') ?_
      simp
    have hG := le_of_mul_le_mul_left hF hn
    simp only [mul_add, Finset.sum_add_distrib]
    linarith
end GlobalTheory.BigOn
