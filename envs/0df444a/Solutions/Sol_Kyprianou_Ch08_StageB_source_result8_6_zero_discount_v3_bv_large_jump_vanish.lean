-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_bv_large_jump_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T20:35:27.580405+00:00
-- url     : https://prove2.me/submissions/97f91b4c-4e78-45a2-bef9-27c89908a8c1

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

private theorem large_jump_vanish_impl :
    ∀ (Ω : Type) [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P),
      Tendsto (fun β : ℝ => ∫ x in Set.Iic (-1 : ℝ),
        ((Real.exp (β * x) - 1) / β) ∂D.triplet.levyMeasure) atTop (𝓝 0) := by
  intro Ω mΩ P hP D
  classical
  let μ : Measure ℝ := D.triplet.levyMeasure
  let F : ℝ → ℝ → ℝ := fun β x => (Real.exp (β * x) - 1) / β
  have hlarge_tend : Tendsto (fun β : ℝ => ∫ x in Iic (-1 : ℝ), F β x ∂μ) atTop
      (𝓝 (∫ x in Iic (-1 : ℝ), (0 : ℝ) ∂μ)) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (l := atTop)
      (μ := μ.restrict (Iic (-1 : ℝ)))
      (F := fun β x => F β x) (f := fun _ : ℝ => 0)
      (fun x : ℝ => min 1 (x ^ 2)) ?_ ?_ ?_ ?_
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with β hβ
      fun_prop
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with β hβ
      filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
      simp only [F, Real.norm_eq_abs]
      have hxle : x ≤ -1 := hx
      have hβpos : 0 < β := lt_of_lt_of_le zero_lt_one hβ
      have hxnonpos : x ≤ 0 := by linarith
      have hn : Real.exp (β * x) ≤ 1 := Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonneg_of_nonpos hβpos.le hxnonpos)
      have hb : |(Real.exp (β * x) - 1) / β| ≤ 1 := by
        rw [abs_div, abs_of_pos hβpos, abs_of_nonpos (sub_nonpos.mpr hn)]
        exact (div_le_one hβpos).mpr (by linarith [Real.exp_pos (β * x)])
      have hm : min 1 (x ^ 2) = 1 := min_eq_left (by nlinarith)
      simpa [hm] using hb
    · have hquad_lint : (∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂μ) < ∞ := by
        simpa [μ] using D.triplet.levyMeasure_isLevyMeasure.2
      have hquad_full : Integrable (fun x : ℝ => min 1 (x ^ 2)) μ := by
        refine ⟨(continuous_const.min (continuous_id.pow 2)).aestronglyMeasurable, ?_⟩
        rw [MeasureTheory.hasFiniteIntegral_iff_ofReal
          (Filter.Eventually.of_forall fun x => le_min zero_le_one (sq_nonneg x))]
        simpa using hquad_lint
      have hquad_restrict : Integrable (fun x : ℝ => min 1 (x ^ 2))
          (μ.restrict (Iic (-1 : ℝ))) := by
        simpa only [MeasureTheory.IntegrableOn] using
          (hquad_full.integrableOn (s := Iic (-1 : ℝ)))
      simpa [μ] using hquad_restrict
    · filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
      have hxle : x ≤ -1 := hx
      have hlin : Tendsto (fun β : ℝ => β * x) atTop atBot := by
        rw [Filter.tendsto_atTop_atBot]
        intro b
        refine ⟨max 0 (-b / (-x)), ?_⟩
        intro β hβ
        have hxpos : 0 < -x := by linarith
        have hbig : -b / (-x) ≤ β := le_trans (le_max_right _ _) hβ
        have hmul : -b ≤ β * (-x) := (div_le_iff₀ hxpos).1 hbig
        have hid : β * x = -(β * (-x)) := by ring
        rw [hid]
        linarith
      have hlim : Tendsto (fun β : ℝ => Real.exp (β * x)) atTop (𝓝 0) := by
        exact Real.tendsto_exp_atBot.comp hlin
      have hdiv : Tendsto (fun β : ℝ => (Real.exp (β * x) - 1) / β) atTop (𝓝 0) := by
        simpa using (hlim.sub tendsto_const_nhds).div_atTop tendsto_id
      simpa [F] using hdiv
  simpa [F, μ] using hlarge_tend

theorem solution :
    ∀ (Ω : Type) [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P),
      Tendsto (fun β : ℝ => ∫ x in Set.Iic (-1 : ℝ),
        ((Real.exp (β * x) - 1) / β) ∂D.triplet.levyMeasure) atTop (𝓝 0) := by
  exact large_jump_vanish_impl
