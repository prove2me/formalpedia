-- Prove2me | solution 1 for MultiPriceOnline.Balance.weak_duality
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:12:39.971644+00:00
-- url     : https://prove2.me/submissions/ef4782bb-c39a-441d-ad7a-44c1c16f80bc

import Mathlib
import Definitions.Def_MultiPriceOnline_Balance_LP

set_option autoImplicit false
open MultiPriceOnline.Balance

theorem solution {ι : Type*} [Fintype ι] (k m : ι → ℕ) (r : ι → ℕ → ℝ) {T : ℕ}
    (p : Fin T → ι → ℕ → ℝ) (x : Fin T → ι → ℕ → ℝ) (hx : LPFeasible k m p x)
    (y : ι → ℝ) (z : Fin T → ℝ) (hyz : DualFeasible m r p y z) :
    lpObj m r p x ≤ dualObj k y z := by
  obtain ⟨h5b, h5c, h5d⟩ := hx
  obtain ⟨h19b, h19y, h19z⟩ := hyz
  unfold lpObj dualObj
  have step1 : ∑ t, ∑ i, ∑ j ∈ Finset.Icc 1 (m i), p t i j * r i j * x t i j ≤
      ∑ t, ∑ i, ∑ j ∈ Finset.Icc 1 (m i), (y i * (p t i j * x t i j) + z t * x t i j) := by
    apply Finset.sum_le_sum; intro t _
    apply Finset.sum_le_sum; intro i _
    apply Finset.sum_le_sum; intro j hj
    rw [Finset.mem_Icc] at hj
    have := mul_le_mul_of_nonneg_right (h19b t i j hj.1 hj.2) (h5d t i j hj.1 hj.2)
    calc p t i j * r i j * x t i j ≤ (p t i j * y i + z t) * x t i j := this
      _ = y i * (p t i j * x t i j) + z t * x t i j := by ring
  have step2 : ∑ t, ∑ i, ∑ j ∈ Finset.Icc 1 (m i), (y i * (p t i j * x t i j) + z t * x t i j) =
      ∑ i, y i * (∑ t, ∑ j ∈ Finset.Icc 1 (m i), p t i j * x t i j) +
        ∑ t, z t * (∑ i, ∑ j ∈ Finset.Icc 1 (m i), x t i j) := by
    simp only [Finset.sum_add_distrib]
    congr 1
    · calc ∑ t, ∑ i, ∑ j ∈ Finset.Icc 1 (m i), y i * (p t i j * x t i j)
          = ∑ t, ∑ i, y i * ∑ j ∈ Finset.Icc 1 (m i), p t i j * x t i j := by
            simp_rw [Finset.mul_sum]
        _ = ∑ i, ∑ t, y i * ∑ j ∈ Finset.Icc 1 (m i), p t i j * x t i j := Finset.sum_comm
        _ = ∑ i, y i * ∑ t, ∑ j ∈ Finset.Icc 1 (m i), p t i j * x t i j := by
            simp_rw [← Finset.mul_sum]
    · apply Finset.sum_congr rfl; intro t _
      simp_rw [Finset.mul_sum]
  have step3 : ∑ i, y i * (∑ t, ∑ j ∈ Finset.Icc 1 (m i), p t i j * x t i j) ≤
      ∑ i, (k i : ℝ) * y i := by
    apply Finset.sum_le_sum; intro i _
    rw [mul_comm ((k i : ℝ))]
    exact mul_le_mul_of_nonneg_left (h5b i) (h19y i)
  have step4 : ∑ t, z t * (∑ i, ∑ j ∈ Finset.Icc 1 (m i), x t i j) ≤ ∑ t, z t := by
    apply Finset.sum_le_sum; intro t _
    calc z t * (∑ i, ∑ j ∈ Finset.Icc 1 (m i), x t i j) ≤ z t * 1 :=
          mul_le_mul_of_nonneg_left (h5c t) (h19z t)
      _ = z t := mul_one _
  linarith
