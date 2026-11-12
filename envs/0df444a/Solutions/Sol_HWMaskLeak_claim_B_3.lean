-- Prove2me | solution 1 for HWMaskLeak.claim_B_3
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-11T12:24:51.724116+00:00
-- url     : https://prove2.me/submissions/8888553e-89b5-4e60-aa44-13c986e418a0

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped BigOperators

theorem solution {ι τ : Type*} [Fintype ι] [Fintype τ] (a : τ → ℝ) (b : ι → τ → ℝ) (μ : ι → ℝ)
    (ha : ∀ t, 0 ≤ a t) (hb : ∀ w t, 0 ≤ b w t) (hμ : ∀ w, 0 ≤ μ w)
    (hμb : ∀ w, μ w = 0 → ∀ t, b w t = 0) (α : ℝ) (hα : 0 ≤ α)
    (hαb : ∀ t, ∑ w ∈ Finset.univ.filter (fun w => 0 < μ w), b w t / μ w ≤ α) :
    ∑ w, Real.sqrt (∑ t, a t * b w t) ≤
      Real.sqrt α * Real.sqrt (∑ w, μ w) * Real.sqrt (∑ t, a t) := by
  classical
  let c : ι → ℝ := fun w => ∑ t, a t * (b w t / μ w)
  have hc : ∀ w, 0 ≤ c w := fun w =>
    Finset.sum_nonneg fun t _ => mul_nonneg (ha t) (div_nonneg (hb w t) (hμ w))
  have hfactor (w : ι) : ∑ t, a t * b w t = μ w * c w := by
    by_cases hz : μ w = 0
    · simp [hz, hμb w hz]
    · simp only [c, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      field_simp
  have hfull (t : τ) : ∑ w, b w t / μ w ≤ α := by
    apply le_trans _ (hαb t)
    simp only [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro w _
    by_cases hp : 0 < μ w
    · simp only [if_pos hp, le_refl]
    · have hz : μ w = 0 := le_antisymm (le_of_not_gt hp) (hμ w)
      simp [hz]
  have hcsum : ∑ w, c w ≤ α * ∑ t, a t := by
    calc
      ∑ w, c w = ∑ t, a t * ∑ w, b w t / μ w := by
        dsimp [c]
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
      _ ≤ ∑ t, a t * α := Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hfull t) (ha t)
      _ = α * ∑ t, a t := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro t _; ring
  calc
    ∑ w, Real.sqrt (∑ t, a t * b w t) = ∑ w, Real.sqrt (μ w) * Real.sqrt (c w) := by
      apply Finset.sum_congr rfl
      intro w _
      rw [hfactor, Real.sqrt_mul (hμ w)]
    _ ≤ Real.sqrt (∑ w, μ w) * Real.sqrt (∑ w, c w) :=
      Real.sum_sqrt_mul_sqrt_le Finset.univ hμ hc
    _ ≤ Real.sqrt (∑ w, μ w) * Real.sqrt (α * ∑ t, a t) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hcsum) (Real.sqrt_nonneg _)
    _ = Real.sqrt α * Real.sqrt (∑ w, μ w) * Real.sqrt (∑ t, a t) := by
      rw [Real.sqrt_mul hα]
      ring

#print axioms solution
