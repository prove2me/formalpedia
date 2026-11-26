-- Prove2me | solution 1 for Kyprianou.Ch04.positiveRewardInfimumSupportBounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:42:34.532998+00:00
-- url     : https://prove2.me/submissions/6a55b1be-a7fb-4fc6-b423-b448937431c8

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- The bounded reward infimum is supported on its positive event. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (g : ℕ → Ω → ℝ) (hm : ∀ n, Measurable (g n))
    (h0 : ∀ n w, 0 ≤ g n w) (h1 : ∀ n w, g n w ≤ 1)
    (B : Set Ω) (hB : ∀ w, w ∈ B ↔ 0 < ⨅ n, g n w) :
    MeasurableSet B ∧
      (∫ w, ⨅ n, g n w ∂P) ≤ (P B).toReal ∧
      (P B = 0 → (∫ w, ⨅ n, g n w ∂P) = 0) := by
  let H : Ω → ℝ := fun w => ⨅ n, g n w
  have hH : Measurable H := Measurable.iInf hm
  have hlo (w : Ω) : 0 ≤ H w := le_ciInf (fun n => h0 n w)
  have hhi (w : Ω) : H w ≤ 1 := by
    have hb : BddBelow (range (fun n => g n w)) := ⟨0, by rintro a ⟨n,rfl⟩; exact h0 n w⟩
    exact (ciInf_le hb 0).trans (h1 0 w)
  have hmeas : MeasurableSet B := by
    have heq : B = {w | 0 < H w} := by ext w; exact hB w
    rw [heq]
    exact measurableSet_lt measurable_const hH
  let b : Ω → ℝ := B.indicator (fun _ => 1)
  have hHi : Integrable H P :=
    (integrable_const (1 : ℝ)).mono hH.aestronglyMeasurable
      (Eventually.of_forall fun w => by
        rw [Real.norm_eq_abs,abs_of_nonneg (hlo w),Real.norm_eq_abs,abs_one]
        exact hhi w)
  have hbi : Integrable b P := (integrable_const (1 : ℝ)).indicator hmeas
  have hle (w : Ω) : H w ≤ b w := by
    by_cases hw : w ∈ B
    · change H w ≤ B.indicator (fun _ => (1 : ℝ)) w
      rw [indicator_of_mem hw]
      exact hhi w
    · change H w ≤ B.indicator (fun _ => (1 : ℝ)) w
      rw [indicator_of_notMem hw]
      exact le_of_not_gt (fun h => hw ((hB w).2 h))
  have hbound := integral_mono hHi hbi hle
  have hbi' : (∫ w, b w ∂P) = (P B).toReal := by
    rw [show b = B.indicator (fun _ => (1 : ℝ)) from rfl,
      integral_indicator hmeas, integral_const]
    simp [Measure.real]
  rw [hbi'] at hbound
  refine ⟨hmeas,hbound,?_⟩
  intro hz
  have hp : 0 ≤ ∫ w, H w ∂P := integral_nonneg hlo
  rw [hz, ENNReal.toReal_zero] at hbound
  exact le_antisymm hbound hp
