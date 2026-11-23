-- Prove2me | solution 1 for Kyprianou.largeJumpProcessLevy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T07:32:46.660069+00:00
-- url     : https://prove2.me/submissions/12c704b0-f4b7-4b57-8800-de47e85642eb

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Theorems.Thm_Kyprianou_finiteRegionPoissonIntegralCh02V3

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (levyMeasure : Measure ℝ) [SigmaFinite levyMeasure]
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure) :
    ProbabilityTheory.IsLevyProcess (Kyprianou.largeJumpProcess P levyMeasure N) P ∧
    ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (Kyprianou.largeJumpProcess P levyMeasure N t)) ξ =
      Complex.exp ((((t : ℝ) : ℂ)) *
        ∫ x in {x : ℝ | 1 ≤ |x|},
          (Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1) ∂levyMeasure) := by
  let B : Set ℝ := {x | 1 ≤ |x|}
  have hB : MeasurableSet B := by
    exact measurableSet_le measurable_const continuous_abs.measurable
  have hfinite : levyMeasure B < ⊤ := by
    let c : ENNReal := ENNReal.ofReal (min 1 ((1 : ℝ) ^ 2))
    let f : ℝ → ENNReal := fun x => ENNReal.ofReal (min 1 (x ^ 2))
    have hc_pos : 0 < c := ENNReal.ofReal_pos.mpr (by norm_num)
    have hf_meas : Measurable f := by
      apply ENNReal.measurable_ofReal.comp
      exact measurable_const.min (measurable_id'.pow_const 2)
    have hsub : B ⊆ {x : ℝ | c ≤ f x} := by
      intro x hx
      simp only [B, Set.mem_setOf_eq] at hx
      simp only [Set.mem_setOf_eq]
      apply ENNReal.ofReal_le_ofReal
      exact min_le_min le_rfl
        ((sq_abs x).symm ▸ pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hx 2)
    have hMarkov := mul_meas_ge_le_lintegral hf_meas c (μ := levyMeasure)
    have hle : c * levyMeasure B ≤ ∫⁻ x, f x ∂levyMeasure :=
      le_trans (mul_le_mul_right (measure_mono hsub) c) hMarkov
    exact ENNReal.lt_top_of_mul_ne_top_right
      (ne_top_of_le_ne_top hlevyMeasure.2.ne hle) hc_pos.ne'
  have hcore :=
    Kyprianou.finiteRegionPoissonIntegralCh02V3
      P levyMeasure N B hB hfinite
  change
    ProbabilityTheory.IsLevyProcess
      (fun t ω => ∫ z in
        (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω)) P ∧
    ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map
        (fun ω => ∫ z in
          (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω))) ξ =
      Complex.exp ((((t : ℝ) : ℂ)) *
        ∫ x in B,
          (Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1) ∂levyMeasure)
  exact hcore
