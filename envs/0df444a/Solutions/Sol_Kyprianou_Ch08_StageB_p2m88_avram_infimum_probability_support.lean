-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m88_avram_infimum_probability_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:53:46.876743+00:00
-- url     : https://prove2.me/submissions/f64d13f5-05c4-4089-aeb1-9d24041ef99e

import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable
import Theorems.Thm_AvramDividend_Classical_levy_path_bddBelow_finite_horizon
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Exponential
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

/-- Source-faithful clock-law reduction. -/
theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (F : Filtration ℝ≥0 mΩ)
      (X : AvramDividend.Classical.SpectrallyNegativeLevy P F),
      ∀ q : ℝ, 0 < q →
      let ν := (P.prod (expMeasure q)).map
        (fun z : Ω × ℝ => -sInf {y : ℝ | ∃ s : ℝ≥0,
        s ≤ z.2.toNNReal ∧ y = X.X s z.1})
      IsProbabilityMeasure ν ∧ ν (Iio 0) = 0 := by
  intro Ω mΩ P hP F X q hq
  dsimp only
  let I : Ω × ℝ → ℝ := fun z : Ω × ℝ => -sInf {y : ℝ | ∃ s : ℝ≥0,
        s ≤ z.2.toNNReal ∧ y = X.X s z.1}
  let M := P.prod (expMeasure q)
  change IsProbabilityMeasure (M.map I) ∧ M.map I (Iio 0) = 0
  letI : IsProbabilityMeasure (expMeasure q) := isProbabilityMeasure_expMeasure hq
  have hI : Measurable I :=
    (AvramDividend.Classical.levy_exponential_real_clock_extrema_drawdown_measurable X).fst.snd
  refine ⟨Measure.isProbabilityMeasure_map hI.aemeasurable, ?_⟩
  rw [Measure.map_apply hI measurableSet_Iio]
  have hE : I ⁻¹' Iio (0 : ℝ) = ∅ := by
    ext z
    constructor
    · intro hz
      have hmem : (0 : ℝ) ∈ {y : ℝ | ∃ s : ℝ≥0,
          s ≤ z.2.toNNReal ∧ y = X.X s z.1} :=
        ⟨0, by positivity, (X.X_zero z.1).symm⟩
      have hb := AvramDividend.Classical.levy_path_bddBelow_finite_horizon X z.2.toNNReal z.1
      have hnonneg : 0 ≤ I z := neg_nonneg.mpr (csInf_le hb hmem)
      exact False.elim (not_lt_of_ge hnonneg hz)
    · intro hz
      exact False.elim hz
  rw [hE, measure_empty]
