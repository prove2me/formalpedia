-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45FullSquareEnergyV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:22:29.086235+00:00
-- url     : https://prove2.me/submissions/2765db75-f1ea-4730-904d-9f22244a73a5

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
open MeasureTheory ProbabilityTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical Topology
set_option autoImplicit false
theorem solution
    (μ : Measure (ℝ × ℝ))
    (h : Integrable (fun z : ℝ × ℝ => min (1 : ℝ) (z.2^2)) μ)
    (hlarge : Integrable (fun z : ℝ × ℝ => z.2^2)
      (μ.restrict {z : ℝ × ℝ | 1/2 < |z.2|})) :
    Integrable (fun z : ℝ × ℝ => z.2^2) μ := by
  let B : Set (ℝ × ℝ) := {z | 1/2 < |z.2|}
  have hB : MeasurableSet B := measurableSet_lt measurable_const measurable_snd.abs
  have hi : Integrable (B.indicator fun z : ℝ × ℝ => z.2^2) μ :=
    (integrable_indicator_iff hB).2 hlarge
  apply (h.add hi).mono' (measurable_snd.pow_const 2).aestronglyMeasurable
  apply Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  change z.2^2 ≤ min 1 (z.2^2) + B.indicator (fun z : ℝ × ℝ => z.2^2) z
  by_cases hz : z ∈ B
  · rw [Set.indicator_of_mem hz]
    linarith [le_min zero_le_one (sq_nonneg z.2)]
  · rw [Set.indicator_of_notMem hz,add_zero]
    have hz' : |z.2| ≤ 1/2 := le_of_not_gt hz
    have hs : z.2^2 ≤ 1 := by
      rw [← sq_abs]
      nlinarith [abs_nonneg z.2]
    rw [min_eq_right hs]
