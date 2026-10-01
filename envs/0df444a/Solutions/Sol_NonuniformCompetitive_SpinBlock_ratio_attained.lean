-- Prove2me | solution 1 for NonuniformCompetitive.SpinBlock.ratio_attained
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T14:43:06.437766+00:00
-- url     : https://prove2.me/submissions/54fa03a6-13e7-46f0-96cd-91abdc841a1a

import Definitions.Def_NonuniformCompetitive_SpinBlock_Randomized
import Mathlib.MeasureTheory.Measure.Stieltjes
import Definitions.Def_NonuniformCompetitive_SpinBlock_blockCDF

open NonuniformCompetitive.SpinBlock MeasureTheory Set
open scoped Interval
namespace SpinProof

theorem denom_pos : 0 < Real.exp 1-1 := by
  have := Real.one_lt_exp_iff.mpr (show (0:ℝ)<1 by norm_num)
  linarith

theorem cdf_continuous (C : ℝ) (hC : 0 < C) : Continuous (blockCDF C) := by
  apply continuous_if_le continuous_id continuous_const (by fun_prop) continuous_const.continuousOn
  intro x hx
  change x=C at hx
  subst x
  simp [hC.ne',denom_pos.ne']

theorem cdf_integral_low (C τ : ℝ) (hC : 0 < C) (hτ : 0 ≤ τ) (hτC : τ ≤ C) :
    ∫ t in (0:ℝ)..τ, (1-blockCDF C t) =
      Real.exp 1/(Real.exp 1-1)*τ-C*(Real.exp (τ/C)-1)/(Real.exp 1-1) := by
  let F : ℝ → ℝ := fun t => Real.exp 1/(Real.exp 1-1)*t-C*(Real.exp (t/C)-1)/(Real.exp 1-1)
  have hd (t : ℝ) : HasDerivAt F (1-(Real.exp (t/C)-1)/(Real.exp 1-1)) t := by
    have h := ((hasDerivAt_id t).div_const C).exp
    have hh := ((hasDerivAt_id t).const_mul (Real.exp 1/(Real.exp 1-1))).sub
      (((h.sub_const 1).const_mul C).div_const (Real.exp 1-1))
    simp only [id_eq,mul_one] at hh
    convert hh using 1 <;> try rfl
    all_goals field_simp [hC.ne',denom_pos.ne'] <;> ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (_ : t ∈ uIcc (0:ℝ) τ) => hd t)
    (show IntervalIntegrable (fun t => 1-(Real.exp (t/C)-1)/(Real.exp 1-1)) volume 0 τ from
      (by fun_prop : Continuous (fun t : ℝ => 1-(Real.exp (t/C)-1)/(Real.exp 1-1))).intervalIntegrable _ _)
  calc
    _ = ∫ t in (0:ℝ)..τ, (1-(Real.exp (t/C)-1)/(Real.exp 1-1)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hτ] at ht
      simp [blockCDF,le_trans ht.2 hτC]
    _ = _ := by simpa [F] using he

theorem cdf_ratio (C τ : ℝ) (hC : 0 < C) (hτ : 0 ≤ τ) :
    blockCDF C τ*C + ∫ t in (0:ℝ)..τ, (1-blockCDF C t) =
      Real.exp 1/(Real.exp 1-1)*min τ C := by
  by_cases ht : τ ≤ C
  · rw [min_eq_left ht,cdf_integral_low C τ hC hτ ht]
    simp only [blockCDF,if_pos ht]
    ring
  · have hCt : C ≤ τ := le_of_lt (not_le.mp ht)
    have hcont : Continuous (fun t => 1-blockCDF C t) := continuous_const.sub (cdf_continuous C hC)
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable 0 C) (hcont.intervalIntegrable C τ)]
    have hi : ∫ t in C..τ, (1-blockCDF C t) = 0 := by
      apply intervalIntegral.integral_zero_ae
      filter_upwards with t
      intro hmem
      rw [uIoc_of_le hCt] at hmem
      simp [blockCDF,not_le.mpr hmem.1]
    rw [hi,cdf_integral_low C C hC hC.le le_rfl,min_eq_right hCt]
    simp [blockCDF,ht,hC.ne']
    field_simp [denom_pos.ne']
    ring

end SpinProof

namespace SpinProof
open NonuniformCompetitive.SpinBlock MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem cdf_mono (C : ℝ) (hC : 0 < C) : Monotone (blockCDF C) := by
  intro x y hxy
  by_cases hy : y ≤ C
  · have hx := hxy.trans hy
    simp only [blockCDF,if_pos hx,if_pos hy]
    apply div_le_div_of_nonneg_right _ denom_pos.le
    exact sub_le_sub_right (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hxy hC.le)) _
  · by_cases hx : x ≤ C
    · simp only [blockCDF,if_pos hx,if_neg hy]
      rw [div_le_iff₀ denom_pos]
      have hh := Real.exp_le_exp.mpr ((div_le_one hC).mpr hx)
      linarith
    · simp [blockCDF,hx,hy]

theorem cdf_zero (C : ℝ) (hC : 0 < C) : blockCDF C 0 = 0 := by simp [blockCDF,hC.le]

theorem cdf_one (C : ℝ) (hC : 0 < C) : blockCDF C C = 1 := by
  simp [blockCDF,hC.ne',denom_pos.ne']

theorem cdf_bounds (C t : ℝ) (hC : 0 < C) (ht : 0 ≤ t) :
    0 ≤ blockCDF C t ∧ blockCDF C t ≤ 1 := by
  refine ⟨?_,?_⟩
  · have h := cdf_mono C hC ht
    rwa [cdf_zero C hC] at h
  · by_cases h : t ≤ C
    · have hh := cdf_mono C hC h
      rwa [cdf_one C hC] at hh
    · simp [blockCDF,h]

noncomputable def cdfSF (C : ℝ) (hC : 0 < C) : StieltjesFunction ℝ where
  toFun t := blockCDF C (max t 0)
  mono' := (cdf_mono C hC).comp (monotone_id.max monotone_const)
  right_continuous' t := ((cdf_continuous C hC).comp (continuous_id.max continuous_const)).continuousAt.continuousWithinAt

theorem sf_continuous (C : ℝ) (hC : 0 < C) : Continuous (cdfSF C hC) :=
  (cdf_continuous C hC).comp (continuous_id.max continuous_const)

theorem sf_atBot (C : ℝ) (hC : 0 < C) : Tendsto (cdfSF C hC) atBot (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_le_atBot (0:ℝ)] with t ht
  simp [cdfSF,max_eq_right ht,cdf_zero C hC]

theorem sf_atTop (C : ℝ) (hC : 0 < C) : Tendsto (cdfSF C hC) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop C] with t ht
  simp [cdfSF,max_eq_left (hC.le.trans ht.le),blockCDF,not_le.mpr ht]

noncomputable def blockLaw (C : ℝ) (hC : 0 < C) : Measure ℝ≥0∞ :=
  Measure.map ENNReal.ofReal (cdfSF C hC).measure

instance blockLaw_prob (C : ℝ) (hC : 0 < C) : IsProbabilityMeasure (blockLaw C hC) := by
  haveI : IsProbabilityMeasure (cdfSF C hC).measure :=
    (cdfSF C hC).isProbabilityMeasure (sf_atBot C hC) (sf_atTop C hC)
  exact Measure.isProbabilityMeasure_map ENNReal.measurable_ofReal.aemeasurable

theorem law_cdf (C : ℝ) (hC : 0 < C) (τ : ℝ≥0) :
    blockLaw C hC (Iio (τ : ℝ≥0∞)) = ENNReal.ofReal (blockCDF C τ) := by
  by_cases hτ : τ = 0
  · subst τ
    simp [cdf_zero C hC]
  · have hτpos : 0 < (τ : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hτ)
    rw [blockLaw,Measure.map_apply ENNReal.measurable_ofReal measurableSet_Iio]
    have he : ENNReal.ofReal ⁻¹' Iio (τ : ℝ≥0∞) = Iio (τ : ℝ) := by
      ext t
      change ENNReal.ofReal t < (τ : ℝ≥0∞) ↔ t < (τ : ℝ)
      rw [← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_lt_ofReal_iff hτpos
    rw [he,(cdfSF C hC).measure_Iio (sf_atBot C hC),
      (sf_continuous C hC).continuousAt.continuousWithinAt.leftLim_eq]
    simp [cdfSF,max_eq_left τ.coe_nonneg]

theorem law_tail (C t : ℝ) (hC : 0 < C) (ht : 0 ≤ t) :
    blockLaw C hC (Ici (ENNReal.ofReal t)) = ENNReal.ofReal (1-blockCDF C t) := by
  have hc : blockLaw C hC (Iio (ENNReal.ofReal t)) = ENNReal.ofReal (blockCDF C t) := by
    rw [ENNReal.ofReal_eq_coe_nnreal ht]
    exact law_cdf C hC (NNReal.mk t ht)
  rw [← compl_Iio,measure_compl measurableSet_Iio (measure_ne_top _ _),measure_univ,hc]
  rw [ENNReal.ofReal_sub 1 (cdf_bounds C t hC ht).1]
  simp

end SpinProof

open NonuniformCompetitive.SpinBlock MeasureTheory Set
open scoped NNReal ENNReal

namespace SpinProof

theorem waitCost_measurable (C : ℝ) (τ : ℝ≥0) : Measurable (fun b => waitCost C b τ) := by
  exact measurable_const.ite (measurableSet_Ici) (measurable_id.add_const _)

theorem min_cost_integral (ν : Measure ℝ≥0∞) (τ : ℝ≥0) :
    ∫⁻ b, min b (τ : ℝ≥0∞) ∂ν = ∫⁻ t in Ioc (0:ℝ) τ, ν (Ici (ENNReal.ofReal t)) := by
  have hne (b : ℝ≥0∞) : min b (τ : ℝ≥0∞) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _)
  have hm : Measurable (fun b : ℝ≥0∞ => (min b (τ : ℝ≥0∞)).toReal) :=
    (measurable_id.min measurable_const).ennreal_toReal
  have hc := lintegral_eq_lintegral_meas_le ν
    (Filter.Eventually.of_forall (fun b : ℝ≥0∞ => ENNReal.toReal_nonneg)) hm.aemeasurable
  simp only [ENNReal.ofReal_toReal (hne _)] at hc
  rw [hc]
  have he : (fun t : ℝ => ν {b : ℝ≥0∞ | t ≤ (min b (τ : ℝ≥0∞)).toReal}) =
      (Iic (τ : ℝ)).indicator (fun t => ν (Ici (ENNReal.ofReal t))) := by
    funext t
    by_cases ht : t ≤ τ
    · rw [indicator_of_mem (show t ∈ Iic (τ : ℝ) from ht)]
      congr 1
      ext b
      rw [mem_setOf_eq,mem_Ici,← ENNReal.ofReal_le_iff_le_toReal (hne b),le_min_iff]
      have hτ : ENNReal.ofReal t ≤ (τ : ℝ≥0∞) := by
        exact (ENNReal.ofReal_le_ofReal ht).trans_eq (by simp)
      simp [hτ]
    · rw [indicator_of_notMem (show t ∉ Iic (τ : ℝ) from ht)]
      have hs : {b : ℝ≥0∞ | t ≤ (min b (τ : ℝ≥0∞)).toReal} = ∅ := by
        ext b
        simp only [mem_setOf_eq,mem_empty_iff_false,iff_false]
        have h : (min b (τ : ℝ≥0∞)).toReal ≤ (τ : ℝ) := by
          simpa using ENNReal.toReal_mono ENNReal.coe_ne_top (min_le_right b (τ : ℝ≥0∞))
        exact not_le.mpr (h.trans_lt (not_le.mp ht))
      rw [hs,measure_empty]
  rw [he,lintegral_indicator measurableSet_Iic,Measure.restrict_restrict measurableSet_Iic]
  rw [show Iic (τ : ℝ) ∩ Ioi (0:ℝ) = Ioc (0:ℝ) (τ:ℝ) by ext t; simp [and_comm] ]

theorem expected_cost (C : ℝ) (ν : Measure ℝ≥0∞) (τ : ℝ≥0) :
    ∫⁻ b, waitCost C b τ ∂ν = ν (Iio (τ : ℝ≥0∞))*ENNReal.ofReal C +
      ∫⁻ t in Ioc (0:ℝ) τ, ν (Ici (ENNReal.ofReal t)) := by
  have he (b : ℝ≥0∞) : waitCost C b τ =
      min b (τ : ℝ≥0∞)+(Iio (τ : ℝ≥0∞)).indicator (fun _ => ENNReal.ofReal C) b := by
    by_cases hb : (τ : ℝ≥0∞) ≤ b
    · simp [waitCost,hb,min_eq_right hb,not_lt.mpr hb]
    · have h := not_le.mp hb
      simp [waitCost,hb,min_eq_left h.le,h]
  simp_rw [he]
  rw [lintegral_add_left (show Measurable (fun b : ℝ≥0∞ => min b (τ : ℝ≥0∞)) from measurable_id.min measurable_const),
    lintegral_indicator_const measurableSet_Iio,min_cost_integral]
  ac_rfl

end SpinProof

namespace SpinProof
open NonuniformCompetitive.SpinBlock MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem law_wait (C : ℝ) (hC : 0 < C) (τ : ℝ≥0) :
    ∫⁻ b, waitCost C b τ ∂blockLaw C hC =
      ENNReal.ofReal (Real.exp 1/(Real.exp 1-1)*min (τ : ℝ) C) := by
  rw [expected_cost,law_cdf]
  have hcont : Continuous (fun t => 1-blockCDF C t) := continuous_const.sub (cdf_continuous C hC)
  have hint : IntegrableOn (fun t => 1-blockCDF C t) (Ioc (0:ℝ) τ) :=
    (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hn : 0 ≤ᵐ[volume.restrict (Ioc (0:ℝ) τ)] (fun t => 1-blockCDF C t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact sub_nonneg.mpr (cdf_bounds C t hC ht.1.le).2
  have he : (∫⁻ t in Ioc (0:ℝ) τ, blockLaw C hC (Ici (ENNReal.ofReal t))) =
      ENNReal.ofReal (∫ t in (0:ℝ)..τ, (1-blockCDF C t)) := by
    rw [intervalIntegral.integral_of_le τ.coe_nonneg,ofReal_integral_eq_lintegral_ofReal hint hn]
    apply setLIntegral_congr_fun measurableSet_Ioc
    intro t ht
    exact law_tail C t hC ht.1.le
  rw [he,← ENNReal.ofReal_mul (cdf_bounds C τ hC τ.coe_nonneg).1,
    ← ENNReal.ofReal_add (mul_nonneg (cdf_bounds C τ hC τ.coe_nonneg).1 hC.le)
      (by rw [intervalIntegral.integral_of_le τ.coe_nonneg]; exact integral_nonneg_of_ae hn),
    cdf_ratio C τ hC τ.coe_nonneg]

noncomputable def optimalAlg (C : ℝ) (hC : 0 < C) : RandomizedAlg C where
  ι := ℝ≥0∞
  μ := blockLaw C hC
  prob := blockLaw_prob C hC
  alg b := ⟨fun _ => b⟩
  meas σ := by
    unfold OnlineAlg.cost
    exact Finset.measurable_sum _ (fun j _ => waitCost_measurable C σ[j])

theorem sum_get (σ : List ℝ≥0) (F : ℝ≥0 → ℝ) :
    ∑ j : Fin σ.length, F σ[j] = (σ.map F).sum := by
  rw [← List.sum_ofFn]
  change (List.ofFn (F ∘ fun j : Fin σ.length => σ[j])).sum = _
  rw [← List.map_ofFn]
  congr 2
  exact List.ofFn_getElem (xs := σ)

theorem attained (C : ℝ) (hC : 0 < C) :
    ∃ A : RandomizedAlg C, A.IsCompetitive (Real.exp 1/(Real.exp 1-1)) := by
  refine ⟨optimalAlg C hC,0,fun σ => ?_⟩
  unfold RandomizedAlg.expCost OnlineAlg.cost
  change (∫⁻ b, ∑ j : Fin σ.length, waitCost C b σ[j] ∂blockLaw C hC) ≤ _
  rw [lintegral_finsetSum _ (fun j _ => waitCost_measurable C σ[j])]
  simp_rw [law_wait C hC]
  have hK : 0 ≤ Real.exp 1/(Real.exp 1-1) := div_nonneg (Real.exp_pos _).le denom_pos.le
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg hK (le_min σ[j].coe_nonneg hC.le)),
    ← Finset.mul_sum,sum_get σ (fun t => min (t : ℝ) C)]
  simp [optCost]

end SpinProof

theorem solution (C : ℝ) (hC : 0 < C) :
    ∃ A : NonuniformCompetitive.SpinBlock.RandomizedAlg C,
      A.IsCompetitive (Real.exp 1/(Real.exp 1-1)) := SpinProof.attained C hC
