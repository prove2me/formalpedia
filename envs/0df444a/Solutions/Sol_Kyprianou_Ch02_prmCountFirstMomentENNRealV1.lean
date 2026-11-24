-- Prove2me | solution 1 for Kyprianou.Ch02.prmCountFirstMomentENNRealV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:42:10.627796+00:00
-- url     : https://prove2.me/submissions/83d2771f-c81d-4026-b4f6-4e5d9683f8e4

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_lintegral_nat_count
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (S : Set (ℝ × ℝ)) (hS : MeasurableSet S) :
    ∫⁻ ω, N.N ω S ∂P = LevyStochCalc.Poisson.referenceIntensity ν S := by
  by_cases h : LevyStochCalc.Poisson.referenceIntensity ν S = ⊤
  · rw [h, lintegral_congr_ae (N.infinite_at_infinite_intensity hS h)]
    simp
  · have hm := N.measurable_eval hS
    have hc : Measurable (fun n : ℕ => (n : ℝ≥0∞)) := measurable_of_countable _
    have h1 : ∫⁻ ω, N.N ω S ∂P = ∫⁻ x, x ∂(P.map (fun ω => N.N ω S)) :=
      (lintegral_map measurable_id hm).symm
    rw [h1, N.poisson_law hS h, LevyStochCalc.Poisson.poissonMeasureENN,
      lintegral_map (f := fun x : ℝ≥0∞ => x) measurable_id hc,
      Kyprianou.ProofPreparation.poisson_lintegral_nat_count, ENNReal.coe_toNNReal h]
