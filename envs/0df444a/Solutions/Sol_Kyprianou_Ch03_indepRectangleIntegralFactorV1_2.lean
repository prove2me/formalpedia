-- Prove2me | solution 2 for Kyprianou.Ch03.indepRectangleIntegralFactorV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T12:58:39.183985+00:00
-- url     : https://prove2.me/submissions/5b9b1210-3b33-48c5-8baf-42818fe3d96e

import Mathlib.Probability.Independence.Integration
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

theorem solution
    {Omega : Type} [mΩ : MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (g h : MeasurableSpace Omega) (hg : g ≤ mΩ) (hh : h ≤ mΩ)
    (hInd : @Indep Omega g h mΩ P)
    (v : Omega → ℝ) (hv : @Measurable Omega ℝ g _ v)
    (B C : Set Omega) (hB : MeasurableSet[g] B) (hC : MeasurableSet[h] C) :
    (∫ x in B ∩ C, v x ∂P) = (∫ x in B, v x ∂P) * ∫ x in C, (1 : ℝ) ∂P := by
  classical
  letI : MeasurableSpace Omega := mΩ
  have hvB : @Measurable Omega ℝ g _ (B.indicator v) := hv.indicator hB
  have hC1 : @Measurable Omega ℝ h _ (C.indicator (fun _ => (1 : ℝ))) :=
    measurable_const.indicator hC
  have hi : IndepFun (B.indicator v) (C.indicator (fun _ => (1 : ℝ))) P := by
    exact indep_of_indep_of_le hInd hvB.comap_le hC1.comap_le
  have hvB0 : @Measurable Omega ℝ mΩ _ (B.indicator v) := fun s hs => hg _ (hvB hs)
  have hC10 : @Measurable Omega ℝ mΩ _ (C.indicator (fun _ => (1 : ℝ))) := fun s hs => hh _ (hC1 hs)
  have he : (B ∩ C).indicator v = B.indicator v * C.indicator (fun _ => (1 : ℝ)) := by
    funext x
    by_cases hx : x ∈ B <;> by_cases hy : x ∈ C <;>
      simp [Set.indicator, hx, hy, Set.mem_inter_iff, Pi.mul_apply]
  rw [← integral_indicator ((hg _ hB).inter (hh _ hC)), he,
    hi.integral_mul_eq_mul_integral hvB0.aestronglyMeasurable hC10.aestronglyMeasurable,
    integral_indicator (hg _ hB), integral_indicator (hh _ hC)]
