-- Prove2me | solution 1 for HDXHitting.fact_2_1_eigenvalue
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:06:08.758207+00:00
-- url     : https://prove2.me/submissions/6e89aeb7-3965-4e60-be8c-2c5a4adb0498

import Mathlib
import Definitions.Def_HDXConc_SecondEigLE

section
set_option autoImplicit false
namespace HDXHitting
theorem chk_fact_2_1_eigenvalue {V : Type*} [Fintype V] (W : V → V → ℝ)
    (hW0 : ∀ u w, 0 ≤ W u w) (hWsymm : ∀ u w, W u w = W w u) (hW1 : ∑ u, ∑ w, W u w = 1)
    (lam : ℝ) (hlam : 0 ≤ lam) (hW : HDXConc.SecondEigLE Finset.univ W lam) (f : V → ℝ)
    (hf : ∀ v, 0 ≤ f v ∧ f v ≤ 1) (μ : ℝ) (hμ : μ = ∑ u, (∑ w, W u w) * f u) :
    ∑ u, ∑ w, W u w * f u * f w ≤ μ ^ 2 + lam * μ * (1 - μ) ∧
      μ ^ 2 + lam * μ * (1 - μ) ≤ μ ^ 2 + lam * μ := by
  classical
  set deg : V → ℝ := fun u => ∑ w, W u w with hdeg
  -- column sums equal degrees
  have hcol : ∀ w, ∑ u, W u w = deg w := fun w => by
    simp only [hdeg]; exact Finset.sum_congr rfl (fun u _ => hWsymm u w)
  have hA : ∑ u, ∑ w, W u w * f u = μ := by
    rw [hμ]; exact Finset.sum_congr rfl (fun u _ => by rw [Finset.sum_mul])
  have hB : ∑ u, ∑ w, W u w * f w = μ := by
    rw [Finset.sum_comm, hμ]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [← Finset.sum_mul, hcol]
  have hdeg1 : ∑ u, deg u = 1 := hW1
  have hg0 : ∑ v ∈ Finset.univ, HDXConc.weightedDeg Finset.univ W v * (f v - μ) = 0 := by
    have : ∀ v, HDXConc.weightedDeg Finset.univ W v = deg v := fun v => rfl
    simp only [this, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hdeg1]
    rw [← hμ]; ring
  have key := hW (fun v => f v - μ) hg0
  have e1 : ∑ u ∈ Finset.univ, ∑ v ∈ Finset.univ, W u v * (f u - μ) * (f v - μ)
      = ∑ u, ∑ w, W u w * f u * f w - μ ^ 2 := by
    have : ∀ u w, W u w * (f u - μ) * (f w - μ)
        = W u w * f u * f w - μ * (W u w * f u) - μ * (W u w * f w) + μ ^ 2 * W u w := by
      intros; ring
    have hW1' : ∑ u, ∑ w, W u w = 1 := hdeg1
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hA, hB, hW1']
    ring
  have hf2 : ∑ v, deg v * f v ^ 2 ≤ μ := by
    rw [hμ]
    exact Finset.sum_le_sum (fun v _ => by
      have h0 : 0 ≤ deg v := Finset.sum_nonneg (fun w _ => hW0 v w)
      have := hf v
      nlinarith [mul_nonneg h0 this.1, mul_nonneg h0 (sub_nonneg.2 this.2), mul_nonneg (mul_nonneg h0 this.1) (sub_nonneg.2 this.2)])
  have e2 : ∑ v ∈ Finset.univ, HDXConc.weightedDeg Finset.univ W v * (f v - μ) ^ 2
      = ∑ v, deg v * f v ^ 2 - μ ^ 2 := by
    have : ∀ v, HDXConc.weightedDeg Finset.univ W v * (f v - μ) ^ 2
        = deg v * f v ^ 2 - 2 * μ * (deg v * f v) + μ ^ 2 * deg v := fun v => by
      show deg v * _ = _; ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hdeg1]
    rw [← hμ]; ring
  rw [e1, e2] at key
  have hμ0 : 0 ≤ lam * μ ^ 2 := mul_nonneg hlam (sq_nonneg _)
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hf2 hlam]
  · nlinarith
end HDXHitting
end

theorem solution : type_of% @HDXHitting.chk_fact_2_1_eigenvalue := @HDXHitting.chk_fact_2_1_eigenvalue
