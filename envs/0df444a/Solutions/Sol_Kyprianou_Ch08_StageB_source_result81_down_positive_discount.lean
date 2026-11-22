-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_down_positive_discount
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T09:52:07.268097+00:00
-- url     : https://prove2.me/submissions/c95b849b-3099-459c-8199-0efc6e91276d

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Exponential
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_filtered_avram_model
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_avram_down_clock_cdf
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_avram_clock_infimum_cdf_laplace
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_scale_from_clock_cdf_laplace
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable
import Theorems.Thm_AvramDividend_Classical_esscher_true_real_clock_reflected_law_nonnegative_support

open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (W : ℝ → ℝ → ℝ) (hW : HasSourceScaleFamily ψ W)
    (q x : ℝ) (hq : 0 < q) :
    downExpectation P D.X q x =
      Zscale q (W q) x - q / Phi ψ q * W q x := by
  classical
  have hScale := hW q hq.le
  have hLargest := hScale.1
  let φ := Phi ψ q
  have hφ0 : 0 ≤ φ := hLargest.2.1.1
  have hroot : ψ φ = q := hLargest.2.1.2
  have hψ0 : ψ 0 = 0 := by
    simpa only [SpectrallyNegativeModel.toData, zero_mul, Real.exp_zero, integral_const,
      probReal_univ, one_smul, Real.log_one, zero_div] using (hψ 0 1 le_rfl zero_lt_one).2
  have hφ : 0 < φ := by
    by_contra! hn
    have hh : φ = 0 := le_antisymm hn hφ0
    rw [hh, hψ0] at hroot
    linarith
  obtain ⟨F, X, hX, hψX⟩ := source_result81_filtered_avram_model Ω P D ψ hψ
  have hrootX : X.ψ φ = q := (hψX φ hφ0).trans hroot
  have hdown (y : ℝ) : downExpectation P X.X q y = downExpectation P D.X q y := by
    unfold downExpectation
    apply integral_congr_ae
    filter_upwards [hX] with ω hω
    simp only [tauMinus, shifted, hω]
  letI : IsProbabilityMeasure (expMeasure q) := isProbabilityMeasure_expMeasure hq
  let R : Ω × ℝ → ℝ := fun z => -sInf {y : ℝ | ∃ s : ℝ≥0,
    s ≤ z.2.toNNReal ∧ y = X.X s z.1}
  let ν := (P.prod (expMeasure q)).map R
  have hR : Measurable R :=
    measurable_snd.comp (measurable_fst.comp
      (levy_exponential_real_clock_extrema_drawdown_measurable X))
  letI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hR.aemeasurable
  have hs : ν (Iio (0 : ℝ)) = 0 :=
    esscher_true_real_clock_reflected_law_nonnegative_support X (P.prod (expMeasure q))
  have hc (β : ℝ) (hβφ : φ < β) :
      IntegrableOn (fun y : ℝ => Real.exp (-β * y) * cdf ν y) (Ioi 0) ∧
      (∫ y in Ioi (0 : ℝ), Real.exp (-β * y) * cdf ν y) =
        (1 / β) * ((q / φ) * ((φ - β) / (q - ψ β))) := by
    have hβ := hφ.trans hβφ
    have h := source_result81_avram_clock_infimum_cdf_laplace X q hq φ hφ hrootX
      β hβ (ne_of_gt hβφ)
    dsimp only at h
    rw [hψX β hβ.le] at h
    exact h
  rw [← hdown x, source_result81_avram_down_clock_cdf X q hq x]
  exact source_result81_scale_from_clock_cdf_laplace ψ (W q) q hq.le hφ hScale ν hs hc x
