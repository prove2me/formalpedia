-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_avram_down_clock_cdf
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T14:42:04.779629+00:00
-- url     : https://prove2.me/submissions/ea635985-d230-4ee2-9fe5-02ef09b2ae0a

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Integral.Prod
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_avram_down_passage_brackets
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_exp_clock_bracket_section

open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    (X : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (q : ℝ) (hq : 0 < q) (x : ℝ) :
    downExpectation P X.X q x = 1 - ProbabilityTheory.cdf
      ((P.prod (ProbabilityTheory.expMeasure q)).map
        (fun z : Ω × ℝ => -sInf {y : ℝ | ∃ s : ℝ≥0,
          s ≤ z.2.toNNReal ∧ y = X.X s z.1})) x := by
  classical
  let Q := expMeasure q
  letI : IsProbabilityMeasure Q := isProbabilityMeasure_expMeasure hq
  let R : Ω × ℝ → ℝ := fun z => -sInf {y : ℝ | ∃ s : ℝ≥0,
    s ≤ z.2.toNNReal ∧ y = X.X s z.1}
  let ν := (P.prod Q).map R
  let B := R ⁻¹' Ioi x
  have hRmeas : Measurable R :=
    measurable_snd.comp (measurable_fst.comp
      (levy_exponential_real_clock_extrema_drawdown_measurable X))
  have hB : MeasurableSet B := hRmeas measurableSet_Ioi
  letI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hRmeas.aemeasurable
  let τ := tauMinus (shifted X.X x) 0
  have hBrackets (ω : Ω) (r : ℝ) :
      (τ ω < (r.toNNReal : WithTop ℝ≥0) → (ω, r) ∈ B) ∧
      ((ω, r) ∈ B → τ ω ≤ (r.toNNReal : WithTop ℝ≥0)) :=
    source_result81_avram_down_passage_brackets X x ω r.toNNReal
  have hsection (ω : Ω) :
      (∫ r, B.indicator (fun _ => (1 : ℝ)) (ω, r) ∂Q) = discountedAt q (τ ω) := by
    let E := (fun r : ℝ => (ω, r)) ⁻¹' B
    have hE : MeasurableSet E := (measurable_const.prodMk measurable_id) hB
    change (∫ r, E.indicator (fun _ => (1 : ℝ)) r ∂Q) = _
    rw [integral_indicator hE, setIntegral_const, smul_eq_mul, mul_one]
    exact source_result81_exp_clock_bracket_section q hq (τ ω) E (hBrackets ω)
  have hInt : Integrable (B.indicator (fun _ => (1 : ℝ))) (P.prod Q) :=
    (integrable_const _).indicator hB
  change (∫ ω, discountedAt q (τ ω) ∂P) = 1 - cdf ν x
  calc
    _ = ∫ ω, ∫ r, B.indicator (fun _ => (1 : ℝ)) (ω, r) ∂Q ∂P :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω => (hsection ω).symm)
    _ = ∫ z, B.indicator (fun _ => (1 : ℝ)) z ∂(P.prod Q) := (integral_prod _ hInt).symm
    _ = ν.real (Ioi x) := by
      rw [integral_indicator hB, setIntegral_const, smul_eq_mul, mul_one]
      simp only [Measure.real_def, ν, Measure.map_apply hRmeas measurableSet_Ioi, B]
    _ = 1 - cdf ν x := by
      rw [Measure.real_def, ← compl_Iic, prob_compl_eq_one_sub measurableSet_Iic,
        ← ofReal_cdf, ← ENNReal.ofReal_one,
        ← ENNReal.ofReal_sub _ (cdf_nonneg (μ := ν) x),
        ENNReal.toReal_ofReal (sub_nonneg.mpr (cdf_le_one (μ := ν) x))]
