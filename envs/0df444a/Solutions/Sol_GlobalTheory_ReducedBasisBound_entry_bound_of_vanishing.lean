-- Prove2me | solution 1 for GlobalTheory.ReducedBasisBound.entry_bound_of_vanishing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:54:08.45389+00:00
-- url     : https://prove2.me/submissions/ea3b1fb5-9bf1-4234-90c2-4e23faa89d9f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_UnipotentUpperInvUpperTriangularBounded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ReducedBasisIntegralConjEntriesBounded
import Theorems.Thm_GlobalTheory_ReducedBasisBound_abs_sum_le_card
import Theorems.Thm_GlobalTheory_ReducedBasisBound_entry_eq

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
theorem _root_.solution (hC : 1 ≤ C₁) (hCm : 0 ≤ Cm) (hT : 0 ≤ T) (ha : ∀ i, 0 < a i)
    (hmn : m * n = 1) (hn : ∀ i j, |n i j| ≤ C₁) (hm : ∀ i j, |m i j| ≤ Cm) (hZ : ∀ i j, |Z i j| ≤ T)
    (M : Matrix (Fin N) (Fin N) ℤ)
    (h1 : diagonal a * n * M.map (Int.cast : ℤ → ℝ) = Z * diagonal a * n)
    (δ : ℝ) (hδ : 0 < δ) (hB : ∀ i j, a i ≤ δ * a j → Z i j = 0) :
    ∀ i j, |(M i j : ℝ)| ≤ N * (Cm * (N * (T * C₁ / δ))) := by
  intro i j
  have hC0 : 0 ≤ C₁ := by linarith
  have hM : M.map (Int.cast : ℤ → ℝ) = m * (n * M.map (Int.cast : ℤ → ℝ)) := by
    rw [← Matrix.mul_assoc, hmn, Matrix.one_mul]
  have hE : ∀ p, |(n * M.map (Int.cast : ℤ → ℝ)) p j| ≤ N * (T * C₁ / δ) := by
    intro p
    have he := entry_eq a n Z _ h1 p j
    have hb : |∑ q, Z p q * a q * n q j| ≤ N * (T * C₁ / δ * a p) := by
      apply abs_sum_le_card
      intro q
      have := ha p
      by_cases hz : Z p q = 0
      · rw [hz]
        simp only [zero_mul, abs_zero]
        positivity
      · have hlt : δ * a q < a p := by
          by_contra hc
          exact hz (hB p q (not_lt.mp hc))
        have haq : a q ≤ a p / δ := by rw [le_div_iff₀ hδ]; linarith
        rw [abs_mul, abs_mul, abs_of_pos (ha q)]
        calc _ ≤ T * (a p / δ) * C₁ :=
              mul_le_mul (mul_le_mul (hZ p q) haq (ha q).le hT) (hn q j) (abs_nonneg _) (by positivity)
          _ = T * C₁ / δ * a p := by ring
    have : a p * |(n * M.map (Int.cast : ℤ → ℝ)) p j| ≤ a p * (N * (T * C₁ / δ)) := by
      rw [← abs_of_pos (ha p), ← abs_mul, he, abs_of_pos (ha p)]
      calc _ ≤ N * (T * C₁ / δ * a p) := hb
        _ = a p * (N * (T * C₁ / δ)) := by ring
    exact le_of_mul_le_mul_left this (ha p)
  have hentry : ((M i j : ℤ) : ℝ) = (M.map (Int.cast : ℤ → ℝ)) i j := by simp
  rw [hentry, hM, mul_apply]
  exact abs_sum_le_card _ _ (fun p => by
    rw [abs_mul]; exact mul_le_mul (hm i p) (hE p) (abs_nonneg _) hCm)
end GlobalTheory.ReducedBasisBound
