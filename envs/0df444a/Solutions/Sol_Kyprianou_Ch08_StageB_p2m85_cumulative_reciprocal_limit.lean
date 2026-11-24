-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m85_cumulative_reciprocal_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T18:45:51.642716+00:00
-- url     : https://prove2.me/submissions/14aa54a8-9a1d-4894-93b6-8f471bea5c90

import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem solution
    (ν : Measure ℝ) (V : ℝ → ℝ) (φ : ℝ) (hφ : 0 ≤ φ)
    (hfin : ∀ z : ℝ, ν (Iic z) < ⊤) (hpos : ν univ ≠ 0)
    (hV : ∀ z : ℝ, Real.exp (-φ*z)*V z = (ν (Iic z)).toReal) :
    Tendsto (fun z : ℝ => (V z)⁻¹) atTop
      (𝓝 (if φ = 0 then ((ν univ)⁻¹).toReal else 0)) := by
  have he : (⋃ z : ℝ, Iic z) = (univ : Set ℝ) := by
    ext z
    simp only [mem_iUnion, mem_Iic, mem_univ, iff_true]
    exact ⟨z, le_rfl⟩
  have ht := tendsto_measure_iUnion_atTop (μ := ν)
    (s := fun z : ℝ => Iic z) (fun _ _ h => Iic_subset_Iic.mpr h)
  rw [he] at ht
  have hi : Tendsto (fun z => ((ν (Iic z))⁻¹).toReal)
      atTop (𝓝 (((ν univ)⁻¹).toReal)) := by
    exact (ENNReal.tendsto_toReal (ENNReal.inv_ne_top.mpr hpos)).comp ht.inv
  have hi' : Tendsto (fun z => ((ν (Iic z)).toReal)⁻¹)
      atTop (𝓝 (((ν univ)⁻¹).toReal)) := by
    simpa only [ENNReal.toReal_inv] using hi
  have heq (z : ℝ) : Real.exp (-φ*z) * ((ν (Iic z)).toReal)⁻¹ = (V z)⁻¹ := by
    rw [← hV, mul_inv_rev, mul_comm (V z)⁻¹, ← mul_assoc, mul_inv_cancel₀ (Real.exp_ne_zero _), one_mul]
  by_cases h : φ = 0
  · simp only [h, if_pos rfl, neg_zero, zero_mul, Real.exp_zero, one_mul] at heq ⊢
    exact hi'.congr' (Eventually.of_forall heq)
  · rw [if_neg h]
    have hx : Tendsto (fun z : ℝ => Real.exp (-φ*z)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr (lt_of_le_of_ne hφ (Ne.symm h))))
    simpa only [zero_mul] using (hx.mul hi').congr' (Eventually.of_forall heq)
