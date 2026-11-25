-- Prove2me | solution 1 for GlobalTheory.FlowProgramme.duality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:28:34.115802+00:00
-- url     : https://prove2.me/submissions/7bdefab4-b9e2-416e-b4cb-af4233e81a44

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_WtSubOneLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CyclicSolvable
import Theorems.Thm_GlobalTheory_FlowProgramme_sum_shift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh
open GlobalTheory GlobalTheory.FlowProgramme
namespace GlobalTheory.FlowProgramme
theorem _root_.solution (l d : ℕ) [NeZero d] (X : ZMod d → ℝ) (hl : 2 ≤ l) (x : ZMod d → ℕ → ℝ)
    (hx : ((∀ a i, 0 ≤ x a i) ∧ (∀ a i, x a i ≠ 0 → Odd i ∧ i < d) ∧ ∀ a, ∑ i ∈ Finset.range d, (l : ℝ) ^ i * x a i + ∑ i ∈ Finset.range d, x (a - i) i ≤ X a)) :
    ((l : ℝ) + 1) * ∑ a, ∑ i ∈ Finset.range d, x a i ≤ ∑ a, X a ∧
      ∀ i₀ : ℕ, ∑ a, ∑ i ∈ Finset.Ico i₀ d, x a i ≤ ((l : ℝ) ^ i₀)⁻¹ * ∑ a, X a := by
  obtain ⟨h0, h1, h2⟩ := hx
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hl1 : (1 : ℝ) ≤ l := by linarith
  have hs := Finset.sum_le_sum (s := Finset.univ) fun a _ => h2 a
  rw [Finset.sum_add_distrib, sum_shift] at hs
  have hT : 0 ≤ ∑ a, ∑ i ∈ Finset.range d, x a i :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun i _ => h0 a i
  constructor
  · have : (l : ℝ) * ∑ a, ∑ i ∈ Finset.range d, x a i
        ≤ ∑ a, ∑ i ∈ Finset.range d, (l : ℝ) ^ i * x a i := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      by_cases h : x a i = 0
      · simp [h]
      · have hi : i ≠ 0 := by
          rintro rfl
          exact absurd (h1 a 0 h).1 (by decide)
        exact mul_le_mul_of_nonneg_right (le_self_pow₀ hl1 hi) (h0 a i)
    linarith
  · intro i₀
    have hp : (0 : ℝ) < (l : ℝ) ^ i₀ := by positivity
    rw [le_inv_mul_iff₀ hp]
    have : (l : ℝ) ^ i₀ * ∑ a, ∑ i ∈ Finset.Ico i₀ d, x a i
        ≤ ∑ a, ∑ i ∈ Finset.range d, (l : ℝ) ^ i * x a i := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun a _ => ?_
      rw [Finset.mul_sum]
      calc ∑ i ∈ Finset.Ico i₀ d, (l : ℝ) ^ i₀ * x a i
          ≤ ∑ i ∈ Finset.Ico i₀ d, (l : ℝ) ^ i * x a i :=
            Finset.sum_le_sum fun i hi =>
              mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hl1 (Finset.mem_Ico.1 hi).1) (h0 a i)
        _ ≤ _ := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ =>
              mul_nonneg (by positivity) (h0 a i)
            intro i hi
            exact Finset.mem_range.2 (Finset.mem_Ico.1 hi).2
    linarith
end GlobalTheory.FlowProgramme
