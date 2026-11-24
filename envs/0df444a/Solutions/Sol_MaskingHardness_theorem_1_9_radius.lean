-- Prove2me | solution 1 for MaskingHardness.theorem_1_9_radius
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T05:10:35.81481+00:00
-- url     : https://prove2.me/submissions/a1c52da3-a50d-49b6-87be-ab3b8a3466e6

import Mathlib
import Definitions.Def_MaskingHardness_IsDist
import Definitions.Def_MaskingHardness_centered
import Definitions.Def_MaskingHardness_lossObjective

open MaskingHardness

theorem solution {X ι : Type*} [Fintype X] [Fintype ι] {k : ℕ}
    (D : X → Fin k → ℝ) (hD : IsDist D) (c : ι → X → Fin k → ℝ)
    (g : Fin k → (Fin k → ℝ) → ℝ) (ε : ℝ) (hε : 0 < ε)
    (v : ℝ) (hv : ∀ y a, v ≤ g y (centered a)) (lam : ι → ℝ)
    (hlam : (∑ x, ∑ y, D x y * g y 0 - v) / ε < ∑ i, |lam i|) :
    MaskingHardness.lossObjective D c g ε 0 < MaskingHardness.lossObjective D c g ε lam := by
  have h0 : lossObjective D c g ε 0 = ∑ x, ∑ y, D x y * g y 0 := by
    have hc : ∀ x, centered (combo c 0 x) = 0 := by
      intro x; funext i; simp [centered, combo]
    simp [lossObjective, hc]
  have hlow : v ≤ ∑ x, ∑ y, D x y * g y (centered (combo c lam x)) := by
    have : ∑ x, ∑ y, D x y * v ≤ ∑ x, ∑ y, D x y * g y (centered (combo c lam x)) := by
      apply Finset.sum_le_sum; intro x _; apply Finset.sum_le_sum; intro y _
      exact mul_le_mul_of_nonneg_left (hv _ _) (hD.1 x y)
    have h1 : ∑ x, ∑ y, D x y * v = v := by
      simp_rw [← Finset.sum_mul, hD.2, one_mul]
    linarith
  have h2 : ∑ x, ∑ y, D x y * g y 0 - v < ε * ∑ i, |lam i| := by
    rw [div_lt_iff₀ hε] at hlam; linarith
  rw [h0]; unfold lossObjective; linarith
