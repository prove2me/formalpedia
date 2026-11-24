-- Prove2me | solution 1 for GlobalTheory.ReducedBasisBound.integral_entry_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:14:08.324206+00:00
-- url     : https://prove2.me/submissions/ee18917c-17fb-4368-9345-b8c3eb5fd2a2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_UnipotentUpperInvUpperTriangularBounded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ReducedBasisIntegralConjEntriesBounded
import Theorems.Thm_GlobalTheory_ReducedBasisBound_abs_sum_le_card
import Theorems.Thm_GlobalTheory_ReducedBasisBound_entry_eq
import Theorems.Thm_GlobalTheory_ReducedBasisBound_int_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open GlobalTheory GlobalTheory.ReducedBasisBound
variable {N : ℕ} {C₁ Cm T : ℝ} {a : Fin N → ℝ} {n m Z : Matrix (Fin N) (Fin N) ℝ}
namespace GlobalTheory.ReducedBasisBound
theorem _root_.solution (hC : 1 ≤ C₁) (hCm : 0 ≤ Cm) (hT : 0 ≤ T)
    (ha : ∀ i, 0 < a i) (hle : ∀ i j, i ≤ j → a i ≤ C₁ * a j)
    (hmn : m * n = 1) (hn_low : ∀ i j, j < i → n i j = 0) (hm_low : ∀ i j, j < i → m i j = 0)
    (hn : ∀ i j, |n i j| ≤ C₁) (hm : ∀ i j, |m i j| ≤ Cm) (hZ : ∀ i j, |Z i j| ≤ T)
    (M' : Matrix (Fin N) (Fin N) ℤ)
    (h2 : diagonal a * n * M'.map (Int.cast : ℤ → ℝ) = Zᵀ * diagonal a * n)
    (ε : ℝ) (hε : 0 < ε) (hK : (N : ℝ) * (Cm * (N * (T * C₁ ^ 3 * ε))) < 1) :
    ∀ i j, a i ≤ ε * a j → M' j i = 0 := by
  intro i j hij
  apply int_eq_zero
  have hC0 : 0 ≤ C₁ := by linarith
  have hM' : M'.map (Int.cast : ℤ → ℝ) = m * (n * M'.map (Int.cast : ℤ → ℝ)) := by
    rw [← Matrix.mul_assoc, hmn, Matrix.one_mul]
  have hE : ∀ p, j ≤ p → |(n * M'.map (Int.cast : ℤ → ℝ)) p i| ≤ N * (T * C₁ ^ 3 * ε) := by
    intro p hp
    have he := entry_eq a n Zᵀ _ h2 p i
    have hb : |∑ q, Zᵀ p q * a q * n q i| ≤ N * (T * C₁ ^ 3 * ε * a p) := by
      apply abs_sum_le_card
      intro q
      rcases le_or_gt q i with hq | hq
      · have haq : a q ≤ C₁ ^ 2 * ε * a p := by
          calc a q ≤ C₁ * a i := hle q i hq
            _ ≤ C₁ * (ε * a j) := by gcongr
            _ ≤ C₁ * (ε * (C₁ * a p)) := by gcongr; exact hle j p hp
            _ = C₁ ^ 2 * ε * a p := by ring
        rw [abs_mul, abs_mul, transpose_apply, abs_of_pos (ha q)]
        calc |Z q p| * a q * |n q i| ≤ T * (C₁ ^ 2 * ε * a p) * C₁ := by
              have := ha p
              exact mul_le_mul (mul_le_mul (hZ q p) haq (ha q).le hT) (hn q i) (abs_nonneg _) (by positivity)
          _ = T * C₁ ^ 3 * ε * a p := by ring
      · rw [hn_low q i hq]
        have := ha p
        simp only [mul_zero, abs_zero]
        positivity
    have : a p * |(n * M'.map (Int.cast : ℤ → ℝ)) p i| ≤ a p * (N * (T * C₁ ^ 3 * ε)) := by
      rw [← abs_of_pos (ha p), ← abs_mul, he, abs_of_pos (ha p)]
      calc _ ≤ N * (T * C₁ ^ 3 * ε * a p) := hb
        _ = a p * (N * (T * C₁ ^ 3 * ε)) := by ring
    exact le_of_mul_le_mul_left this (ha p)
  have hentry : ((M' j i : ℤ) : ℝ) = (M'.map (Int.cast : ℤ → ℝ)) j i := by simp
  rw [hentry, hM', mul_apply]
  refine lt_of_le_of_lt (abs_sum_le_card _ _ (fun p => ?_)) hK
  rcases le_or_gt j p with hp | hp
  · rw [abs_mul]
    exact mul_le_mul (hm j p) (hE p hp) (abs_nonneg _) hCm
  · rw [hm_low j p hp, zero_mul, abs_zero]
    have : (0 : ℝ) ≤ N * (T * C₁ ^ 3 * ε) := by positivity
    positivity
end GlobalTheory.ReducedBasisBound
