-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_avram_clock_infimum_cdf_laplace
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T10:31:14.339897+00:00
-- url     : https://prove2.me/submissions/107b01f0-dd52-4a08-9153-8daf87452a4a

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Exponential
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_clock_drawdown_infimum_marginal_law
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_clock_descending_mgf_all_beta
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable
import Theorems.Thm_AvramDividend_Classical_esscher_true_real_clock_reflected_law_nonnegative_support
import Theorems.Thm_AvramDividend_Classical_esscher_probability_weighted_cdf_real_eq_laplace

open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    (X : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (q : ℝ) (hq : 0 < q) (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (β : ℝ) (hβ : 0 < β) (hne : β ≠ φ) :
    let ν := (P.prod (expMeasure q)).map
      (fun z : Ω × ℝ => -sInf {y : ℝ | ∃ s : ℝ≥0,
        s ≤ z.2.toNNReal ∧ y = X.X s z.1})
    IntegrableOn (fun y : ℝ => Real.exp (-β * y) * cdf ν y) (Ioi 0) ∧
      (∫ y in Ioi (0 : ℝ), Real.exp (-β * y) * cdf ν y) =
        (1 / β) * ((q / φ) * ((φ - β) / (q - X.ψ β))) := by
  intro ν
  letI : IsProbabilityMeasure (expMeasure q) := isProbabilityMeasure_expMeasure hq
  let M := P.prod (expMeasure q)
  let A := fun z : Ω × ℝ => runningSup X z.2.toNNReal z.1 - X.X z.2.toNNReal z.1
  have hmeas := levy_exponential_real_clock_extrema_drawdown_measurable X
  have hA : Measurable A := measurable_snd.comp hmeas
  letI : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map (measurable_snd.comp (measurable_fst.comp hmeas)).aemeasurable
  have hs : ν {a : ℝ | a < 0} = 0 := by
    simpa only [Iio] using
      esscher_true_real_clock_reflected_law_nonnegative_support X M
  have hνnonneg : ∀ᵐ y ∂ν, 0 ≤ y := by
    rw [ae_iff]
    simpa only [not_le] using hs
  have hLaw : M.map A = ν := by
    simpa only [M, A, ν, X.X_zero, zero_add] using
      avram_ws01e_bt_new_original_clock_drawdown_infimum_marginal_law X q hq
  let w := fun y : ℝ => Real.exp (-β * y)
  have hw : Measurable w := Real.measurable_exp.comp (measurable_const.mul measurable_id)
  have hwν : Integrable w ν := by
    refine (integrable_const (1 : ℝ)).mono' hw.aestronglyMeasurable ?_
    filter_upwards [hνnonneg] with y hy
    change ‖Real.exp (-β * y)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hβ.le) hy)
  have hwvol : Integrable w (volume.restrict (Ioi (0 : ℝ))) :=
    integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hβ) 0
  have hcmeas : Measurable (cdf ν) := (monotone_cdf (μ := ν)).measurable
  have hc : Integrable (fun y => w y * cdf ν y) (volume.restrict (Ioi (0 : ℝ))) := by
    refine hwvol.mono' (hw.mul hcmeas).aestronglyMeasurable ?_
    filter_upwards with y
    change ‖Real.exp (-β * y) * cdf ν y‖ ≤ Real.exp (-β * y)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (cdf_nonneg (μ := ν) y))]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (cdf_le_one (μ := ν) y) (Real.exp_pos (-β * y)).le
  have hw0 (y : ℝ) : 0 ≤ w y := (Real.exp_pos _).le
  have hc0 (y : ℝ) : 0 ≤ w y * cdf ν y := mul_nonneg (hw0 y) (cdf_nonneg (μ := ν) y)
  have hdiv : 0 ≤ 1 / β := div_nonneg zero_le_one hβ.le
  have hCDF := esscher_probability_weighted_cdf_real_eq_laplace ν hs β hβ
  change ENNReal.ofReal (∫ y in Ioi (0 : ℝ), w y * cdf ν y) =
    ENNReal.ofReal (1 / β) * (∫⁻ y, ENNReal.ofReal (w y) ∂ν) at hCDF
  rw [← ofReal_integral_eq_lintegral_ofReal hwν (Eventually.of_forall hw0),
    ← ENNReal.ofReal_mul hdiv] at hCDF
  have hReal := congrArg ENNReal.toReal hCDF
  simp only [ENNReal.toReal_ofReal (integral_nonneg hc0),
    ENNReal.toReal_ofReal (mul_nonneg hdiv (integral_nonneg hw0))] at hReal
  obtain ⟨_, _, _, hmgf⟩ := avram_ws01e_bt_new_original_clock_descending_mgf_all_beta X q hq φ hφ hroot
  have hwEq : (∫ y, w y ∂ν) = mgf (fun z => -A z) M β := by
    rw [← hLaw, integral_map hA.aemeasurable hw.aestronglyMeasurable, mgf]
    simp only [w, mul_neg, neg_mul]
  have hβmgf := hmgf β hβ
  rw [if_neg hne] at hβmgf
  change mgf (fun z => -A z) M β = _ at hβmgf
  exact ⟨hc, by rw [hReal, hwEq, hβmgf]⟩
