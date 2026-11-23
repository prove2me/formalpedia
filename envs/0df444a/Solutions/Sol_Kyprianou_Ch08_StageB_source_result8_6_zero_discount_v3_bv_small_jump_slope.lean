-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_bv_small_jump_slope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T19:58:59.043702+00:00
-- url     : https://prove2.me/submissions/588f3a86-7ddd-4aa6-96a3-4ad229ed78eb

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

private theorem small_jump_slope_impl :
    ∀ (Ω : Type) [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P),
      HasBoundedVariationTriplet D.gaussianCoefficient D.triplet.levyMeasure →
      Tendsto (fun β : ℝ => ∫ x in Set.Ioo (-1 : ℝ) 0,
        ((Real.exp (β * x) - 1) / β - x) ∂D.triplet.levyMeasure) atTop
        (𝓝 (-∫ x in Set.Ioo (-1 : ℝ) 0, x ∂D.triplet.levyMeasure)) := by
  intro Ω mΩ P hP D hbv
  classical
  let μ : Measure ℝ := D.triplet.levyMeasure
  let F : ℝ → ℝ → ℝ := fun β x => (Real.exp (β * x) - 1) / β - x
  have hsmall_dom : Integrable (fun x : ℝ => 2 * |x|) (μ.restrict (Ioo (-1 : ℝ) 0)) := by
    have hbf : (∫⁻ x in Ioo (-1 : ℝ) 0, ENNReal.ofReal |x| ∂μ) < ∞ := by
      simpa [μ] using hbv.2
    have hbf' : (∫⁻ x, ENNReal.ofReal |x| ∂(μ.restrict (Ioo (-1 : ℝ) 0))) < ∞ := by
      simpa using hbf
    have hfi_abs : HasFiniteIntegral (fun x : ℝ => 2 * |x|)
        (μ.restrict (Ioo (-1 : ℝ) 0)) := by
      rw [MeasureTheory.hasFiniteIntegral_iff_ofReal
        (Filter.Eventually.of_forall fun x : ℝ =>
          mul_nonneg (by norm_num) (abs_nonneg x))]
      calc
        (∫⁻ x, ENNReal.ofReal (2 * |x|) ∂(μ.restrict (Ioo (-1 : ℝ) 0))) =
            ∫⁻ x, (2 : ℝ≥0∞) * ENNReal.ofReal |x| ∂(μ.restrict (Ioo (-1 : ℝ) 0)) := by
          congr with x
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num
        _ = (2 : ℝ≥0∞) * ∫⁻ x, ENNReal.ofReal |x| ∂(μ.restrict (Ioo (-1 : ℝ) 0)) := by
          rw [MeasureTheory.lintegral_const_mul' (2 : ℝ≥0∞) _ (by norm_num)]
        _ < ∞ := ENNReal.mul_lt_top (by norm_num) hbf'
    exact ⟨(continuous_const.mul continuous_abs).aestronglyMeasurable.restrict, hfi_abs⟩
  have hsmall_tend : Tendsto (fun β : ℝ => ∫ x in Ioo (-1 : ℝ) 0, F β x ∂μ)
      atTop (𝓝 (∫ x in Ioo (-1 : ℝ) 0, (-x) ∂μ)) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := μ.restrict (Ioo (-1 : ℝ) 0))
      (F := fun β x => F β x) (f := fun x : ℝ => -x)
      (fun x : ℝ => 2 * |x|) ?_ ?_ hsmall_dom ?_
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with β hβ
      fun_prop
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with β hβ
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      simp only [F, Real.norm_eq_abs]
      have hxneg : x < 0 := hx.2
      have hβpos : 0 < β := lt_of_lt_of_le zero_lt_one hβ
      have h₁ : |(Real.exp (β * x) - 1) / β| ≤ |x| := by
        rw [abs_div, abs_of_pos hβpos]
        have hle : 1 - Real.exp (β * x) ≤ β * (-x) := by
          have := Real.add_one_le_exp (β * x)
          linarith
        have hn : Real.exp (β * x) ≤ 1 :=
          Real.exp_le_one_iff.mpr
            (mul_nonpos_of_nonneg_of_nonpos (le_trans zero_le_one hβ) hxneg.le)
        rw [abs_of_nonpos (sub_nonpos.mpr hn)]
        rw [abs_of_neg hxneg]
        have hle' : -(Real.exp (β * x) - 1) ≤ -x * β := by nlinarith [hle]
        exact (div_le_iff₀ hβpos).2 hle'
      have hF : |(Real.exp (β * x) - 1) / β - x| ≤ 2 * |x| := by
        have hxabs : x ≤ |x| := le_abs_self x
        have hnegxabs : -x ≤ |x| := by simpa using (le_abs_self (-x))
        rw [abs_le]
        constructor <;>
          linarith [neg_abs_le ((Real.exp (β * x) - 1) / β),
            le_abs_self ((Real.exp (β * x) - 1) / β), h₁, hxabs, hnegxabs]
      simpa [F] using hF
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      have hxneg : x < 0 := hx.2
      have hlin : Tendsto (fun β : ℝ => β * x) atTop atBot := by
        rw [Filter.tendsto_atTop_atBot]
        intro b
        refine ⟨max 0 (-b / (-x)), ?_⟩
        intro β hβ
        have hxpos : 0 < -x := neg_pos.mpr hxneg
        have hbig : -b / (-x) ≤ β := le_trans (le_max_right _ _) hβ
        have hmul : -b ≤ β * (-x) := (div_le_iff₀ hxpos).1 hbig
        have hid : β * x = -(β * (-x)) := by ring
        rw [hid]
        linarith
      have hlim : Tendsto (fun β : ℝ => Real.exp (β * x)) atTop (𝓝 0) := by
        exact Real.tendsto_exp_atBot.comp hlin
      have hdiv : Tendsto (fun β : ℝ => (Real.exp (β * x) - 1) / β) atTop (𝓝 0) := by
        simpa using (hlim.sub tendsto_const_nhds).div_atTop tendsto_id
      simpa [F, hx.1, hxneg] using hdiv.sub tendsto_const_nhds
  have hnegint : (∫ x in Ioo (-1 : ℝ) 0, (-x) ∂μ) =
      -(∫ x in Ioo (-1 : ℝ) 0, x ∂μ) := by
    exact MeasureTheory.integral_neg (μ := μ.restrict (Ioo (-1 : ℝ) 0))
      (f := fun x : ℝ => x)
  rw [hnegint] at hsmall_tend
  simpa [F, μ] using hsmall_tend

theorem solution :
    ∀ (Ω : Type) [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P),
      HasBoundedVariationTriplet D.gaussianCoefficient D.triplet.levyMeasure →
      Tendsto (fun β : ℝ => ∫ x in Set.Ioo (-1 : ℝ) 0,
        ((Real.exp (β * x) - 1) / β - x) ∂D.triplet.levyMeasure) atTop
        (𝓝 (-∫ x in Set.Ioo (-1 : ℝ) 0, x ∂D.triplet.levyMeasure)) := by
  exact small_jump_slope_impl
