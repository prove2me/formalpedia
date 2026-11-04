-- Prove2me | solution 1 for LostSalesOrderUpTo.Asymptotic.order_up_to_asymptotically_optimal
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T05:11:57.946237+00:00
-- url     : https://prove2.me/submissions/aae29978-a8e1-42f0-a6ab-08db7e55c610

import Theorems.Thm_LostSalesOrderUpTo_Asymptotic_theorem15a
import Theorems.Thm_LostSalesOrderUpTo_Asymptotic_lemma13
import Definitions.Def_LostSalesOrderUpTo_Asymptotic_Backorder
import Theorems.Thm_LostSalesOrderUpTo_Asymptotic_newsvendor_optimal
import Theorems.Thm_RiskFunctionals_AVaR_alpha_bounds_tail_probs
import Theorems.Thm_ProbabilityTheory_nonempty_setOf_le_cdf


noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators
open LostSalesOrderUpTo.Asymptotic

namespace RatioLimitAnalysis

lemma eq_dirac_of_holding_shortfall_zero (μ : Measure ℝ≥0) [IsProbabilityMeasure μ]
    (hmean : Integrable (fun d : ℝ≥0 => (d : ℝ)) μ) (S : ℝ≥0)
    (hH : expectedHolding μ S = 0) (hB : expectedShortfall μ S = 0) :
    μ = Measure.dirac S := by
  have hHi : Integrable (fun d : ℝ≥0 => max ((S : ℝ) - (d : ℝ)) 0) μ :=
    ((integrable_const _).sub hmean).pos_part
  have hBi : Integrable (fun d : ℝ≥0 => max ((d : ℝ) - (S : ℝ)) 0) μ :=
    (hmean.sub (integrable_const _)).pos_part
  have haH := (integral_eq_zero_iff_of_nonneg (fun _ => le_max_right _ _) hHi).mp hH
  have haB := (integral_eq_zero_iff_of_nonneg (fun _ => le_max_right _ _) hBi).mp hB
  have ha : (fun d : ℝ≥0 => d) =ᵐ[μ] (fun _ => S) := by
    filter_upwards [haH, haB] with d hdH hdB
    apply NNReal.coe_injective
    have h1 := le_max_left ((S : ℝ) - (d : ℝ)) 0
    have h2 := le_max_left ((d : ℝ) - (S : ℝ)) 0
    change max ((S : ℝ) - (d : ℝ)) 0 = 0 at hdH
    change max ((d : ℝ) - (S : ℝ)) 0 = 0 at hdB
    linarith
  calc
    μ = μ.map (fun d : ℝ≥0 => d) := Measure.map_id.symm
    _ = μ.map (fun _ => S) := Measure.map_congr ha
    _ = Measure.dirac S := by simp

lemma holding_pos_of_shortfall_eq_zero (μ : Measure ℝ≥0) [IsProbabilityMeasure μ]
    (hmean : Integrable (fun d : ℝ≥0 => (d : ℝ)) μ)
    (hnonconstant : ¬ ∃ d : ℝ≥0, μ = Measure.dirac d)
    (S : ℝ≥0) (hB : expectedShortfall μ S = 0) : 0 < expectedHolding μ S := by
  have hn : 0 ≤ expectedHolding μ S := integral_nonneg (fun _ => le_max_right _ _)
  apply lt_of_le_of_ne hn
  intro heq
  exact hnonconstant ⟨S, eq_dirac_of_holding_shortfall_zero μ hmean S heq.symm hB⟩

/-- Bounded optimum costs force shortage charges to vanish at any family of optimizers. -/
lemma ratio_and_holding_pos_of_bounded_optima (H B : ℝ → ℝ) (h : ℝ)
    (hB : ∀ b, 0 ≤ B b)
    (hopt : ∀ b, 0 < b → ∀ k, 0 < k →
      h * H b + b * B b ≤ h * H k + b * B k)
    (hpos : 0 < h * H 1 + B 1)
    (hbound : ∃ M, ∀ b, 0 < b → h * H b + b * B b ≤ M) :
    Tendsto (fun b => b * B b / (h * H b)) atTop (nhds 0) ∧
      ∀ᶠ b in atTop, 0 < h * H b := by
  let C : ℝ → ℝ := fun b => h * H b + b * B b
  let F : ℝ → ℝ := fun b => C (max b 1)
  have hmono : Monotone F := by
    intro b k hbk
    have hb : 0 < max b 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have hk : 0 < max k 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have hh := hopt (max b 1) hb (max k 1) hk
    have hm := mul_le_mul_of_nonneg_right (max_le_max_right 1 hbk) (hB (max k 1))
    dsimp only [F, C]
    linarith
  obtain ⟨M, hM⟩ := hbound
  have hbounded : BddAbove (Set.range F) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨b, rfl⟩
    exact hM (max b 1) (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
  have hF : Tendsto F atTop (nhds (⨆ b, F b)) := tendsto_atTop_ciSup hmono hbounded
  let ell : ℝ := ⨆ b, F b
  have hC : Tendsto C atTop (nhds ell) := by
    apply hF.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with b hb
    dsimp [F]
    rw [max_eq_left hb]
  have hell : 0 < ell := by
    have hle : F 1 ≤ ell := le_ciSup hbounded 1
    have hf1 : F 1 = h * H 1 + B 1 := by simp [F, C]
    rw [hf1] at hle
    exact hpos.trans_le hle
  have hhalf : Tendsto (fun b : ℝ => C (b / 2)) atTop (nhds ell) :=
    hC.comp (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2))
  have hcharge : Tendsto (fun b => b * B b) atTop (nhds 0) := by
    apply squeeze_zero'
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with b hb
      exact mul_nonneg (by linarith) (hB b)
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with b hb
      have hbp : 0 < b := by linarith
      have ho := hopt (b / 2) (by positivity) b hbp
      change b * B b ≤ 2 * (C b - C (b / 2))
      dsimp only [C]
      linarith
    · simpa using (hC.sub hhalf).const_mul 2
  have hholding : Tendsto (fun b => h * H b) atTop (nhds ell) := by
    have ht := hC.sub hcharge
    simpa [C] using ht
  constructor
  · convert hcharge.div hholding hell.ne' using 1
    · ext b
      simp
    · simp
  · exact hholding.eventually (eventually_gt_nhds hell)

lemma newsvendor_cost_le (μ : Measure ℝ≥0) [IsProbabilityMeasure μ]
    (h b : ℝ) (hh : 0 < h) (hb : 0 < b)
    (hmean : Integrable (fun d : ℝ≥0 => (d : ℝ)) μ) (S : ℝ≥0) :
    backorderCost μ h b (newsvendorLevel μ h b) ≤ backorderCost μ h b S := by
  rw [newsvendor_optimal μ h b hh hb hmean]
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro _ ⟨T, rfl⟩
    exact add_nonneg
      (mul_nonneg hh.le (integral_nonneg (fun _ => le_max_right _ _)))
      (mul_nonneg hb.le (integral_nonneg (fun _ => le_max_right _ _)))
  · exact ⟨S, rfl⟩

/-- The bounded-demand branch does not require a mean-residual-life hypothesis. -/
lemma ratio_and_holding_pos_of_bounded_demand (μ : Measure ℝ≥0) [IsProbabilityMeasure μ]
    (h : ℝ) (hh : 0 < h)
    (hmean : Integrable (fun d : ℝ≥0 => (d : ℝ)) μ)
    (hnonconstant : ¬ ∃ d : ℝ≥0, μ = Measure.dirac d)
    (hbounded : ∃ M : ℝ≥0, expectedShortfall μ M = 0) :
    Tendsto (fun b : ℝ => shortageHoldingRatio μ h b (newsvendorLevel μ h b))
      atTop (nhds 0) ∧
    ∀ᶠ b in atTop, 0 < expectedHolding μ (newsvendorLevel μ h b) := by
  let H : ℝ → ℝ := fun b => expectedHolding μ (newsvendorLevel μ h b)
  let B : ℝ → ℝ := fun b => expectedShortfall μ (newsvendorLevel μ h b)
  have hH (b : ℝ) : 0 ≤ H b := integral_nonneg (fun _ => le_max_right _ _)
  have hB (b : ℝ) : 0 ≤ B b := integral_nonneg (fun _ => le_max_right _ _)
  have hopt : ∀ b, 0 < b → ∀ k, 0 < k →
      h * H b + b * B b ≤ h * H k + b * B k := by
    intro b hb k _
    exact newsvendor_cost_le μ h b hh hb hmean (newsvendorLevel μ h k)
  have hpos : 0 < h * H 1 + B 1 := by
    by_contra hn
    have hle : h * H 1 + B 1 ≤ 0 := le_of_not_gt hn
    have hzH : H 1 = 0 := by nlinarith [hH 1, hB 1]
    have hzB : B 1 = 0 := by nlinarith [hH 1, hB 1]
    exact hnonconstant ⟨newsvendorLevel μ h 1,
      eq_dirac_of_holding_shortfall_zero μ hmean _ hzH hzB⟩
  have hbound : ∃ M, ∀ b, 0 < b → h * H b + b * B b ≤ M := by
    obtain ⟨M, hM⟩ := hbounded
    refine ⟨h * expectedHolding μ M, ?_⟩
    intro b hb
    have hc := newsvendor_cost_le μ h b hh hb hmean M
    simpa only [backorderCost, hM, mul_zero, add_zero] using hc
  obtain ⟨hratio, hholding⟩ :=
    ratio_and_holding_pos_of_bounded_optima H B h hB hopt hpos hbound
  refine ⟨hratio, ?_⟩
  filter_upwards [hholding] with b hb
  exact (mul_pos_iff_of_pos_left hh).mp hb

end RatioLimitAnalysis


noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators
open LostSalesOrderUpTo.Asymptotic

namespace LostSalesRatioUnbounded

lemma quantile_cdf_lower (μ : Measure ℝ≥0) [IsProbabilityMeasure μ]
    (h b : ℝ) (hh : 0 < h) (hb : 0 < b) :
    b / (b+h) ≤ μ.real (Set.Iic (newsvendorLevel μ h b)) := by
  let α : ℝ := b / (b + h)
  let Y : ℝ≥0 → ℝ := fun d ↦ (d : ℝ)
  have hY : Measurable Y := by fun_prop
  have hα₀ : 0 < α := div_pos hb (add_pos hb hh)
  have hα₁ : α < 1 := (div_lt_one (add_pos hb hh)).2 (by linarith)
  letI : IsProbabilityMeasure (μ.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
  have hfin : ∃ u : ℝ, α ≤ RiskFunctionals.AVaR.distributionFunction (μ.map Y) u := by
    obtain ⟨u, hu⟩ := ProbabilityTheory.nonempty_setOf_le_cdf (μ.map Y) hα₁
    exact ⟨u, by simpa only [Set.mem_setOf_eq, ProbabilityTheory.cdf_eq_real,
      RiskFunctionals.AVaR.distributionFunction] using hu⟩
  have hdist (S : ℝ≥0) :
      RiskFunctionals.AVaR.distributionFunction (μ.map Y) (S : ℝ) =
        (distribution μ S).toReal := by
    rw [RiskFunctionals.AVaR.distributionFunction, measureReal_def,
      Measure.map_apply hY measurableSet_Iic]
    rfl
  have hnonneg (x : ℝ)
      (hx : α ≤ RiskFunctionals.AVaR.distributionFunction (μ.map Y) x) : 0 ≤ x := by
    by_contra hn
    have hxneg : x < 0 := lt_of_not_ge hn
    have hempty : Y ⁻¹' Set.Iic x = ∅ := by
      ext d
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false, iff_false]
      exact not_le_of_gt (lt_of_lt_of_le hxneg d.property)
    have hzero : RiskFunctionals.AVaR.distributionFunction (μ.map Y) x = 0 := by
      rw [RiskFunctionals.AVaR.distributionFunction, measureReal_def,
        Measure.map_apply hY measurableSet_Iic, hempty]
      simp
    rw [hzero] at hx
    exact (not_le_of_gt hα₀) hx
  have hset :
      ((↑) : ℝ≥0 → ℝ) '' {S : ℝ≥0 | ENNReal.ofReal α ≤ distribution μ S} =
        {x : ℝ | α ≤ RiskFunctionals.AVaR.distributionFunction (μ.map Y) x} := by
    ext x
    constructor
    · rintro ⟨S, hS, rfl⟩
      change α ≤ RiskFunctionals.AVaR.distributionFunction (μ.map Y) (S : ℝ)
      rw [hdist]
      exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ _)).1 hS
    · intro hx
      let S : ℝ≥0 := ⟨x, hnonneg x hx⟩
      refine ⟨S, ?_, rfl⟩
      apply (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ _)).2
      change α ≤ (distribution μ S).toReal
      rw [← hdist S]
      exact hx
  have hquantile : (newsvendorLevel μ h b : ℝ) =
      RiskFunctionals.AVaR.quantileFunction (μ.map Y) α := by
    rw [newsvendorLevel, NNReal.coe_sInf]
    exact congrArg sInf hset
  have hbounds := RiskFunctionals.AVaR.alpha_bounds_tail_probs μ Y hY α hα₀ hα₁.le hfin
  have hCDF : α ≤ μ.real {d | Y d ≤ RiskFunctionals.AVaR.quantileFunction (μ.map Y) α} := by
    rw [hbounds.2.2.2.2.1]
    exact hbounds.2.2.2.1
  rw [← hquantile] at hCDF
  have hsetCDF : {d : ℝ≥0 | Y d ≤ (newsvendorLevel μ h b : ℝ)} =
      Set.Iic (newsvendorLevel μ h b) := by
    ext d
    simp only [Set.mem_setOf_eq, Set.mem_Iic, Y, NNReal.coe_le_coe]
  rw [hsetCDF] at hCDF
  exact hCDF

lemma tail_add_cdf (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] (S : ℝ≥0) :
    μ.real (Set.Ioi S) + μ.real (Set.Iic S) = 1 := by
  simpa only [Set.compl_Iic, probReal_univ, add_comm] using
    (measureReal_add_measureReal_compl (μ := μ) (s := Set.Iic S) measurableSet_Iic)

lemma shortfall_zero_of_tail_zero (μ : Measure ℝ≥0) [IsProbabilityMeasure μ]
    (S : ℝ≥0) (hz : μ.real (Set.Ioi S) = 0) : expectedShortfall μ S = 0 := by
  have hz' : μ (Set.Ioi S) = 0 := (measureReal_eq_zero_iff (measure_ne_top μ _)).mp hz
  have hae : ∀ᵐ d ∂μ, d ≤ S := by
    apply ae_iff.mpr
    have hset : {d : ℝ≥0 | ¬ d ≤ S} = Set.Ioi S := by
      ext d
      simp only [Set.mem_setOf_eq, Set.mem_Ioi, not_le]
    rwa [hset]
  unfold expectedShortfall
  calc
    _ = ∫ _d : ℝ≥0, (0 : ℝ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hae] with d hd
      exact max_eq_right (sub_nonpos.mpr (NNReal.coe_le_coe.mpr hd))
    _ = 0 := by simp

lemma tail_pos (μ : Measure ℝ≥0) [IsProbabilityMeasure μ]
    (hunbounded : ¬ ∃ M : ℝ≥0, expectedShortfall μ M = 0) (S : ℝ≥0) :
    0 < μ.real (Set.Ioi S) := by
  by_contra hn
  have hz : μ.real (Set.Ioi S) = 0 :=
    le_antisymm (not_lt.mp hn) measureReal_nonneg
  exact hunbounded ⟨S, shortfall_zero_of_tail_zero μ S hz⟩

lemma fractile_tendsto (h : ℝ) :
    Tendsto (fun b : ℝ => b / (b+h)) atTop (nhds 1) := by
  have hden : Tendsto (fun b : ℝ => b+h) atTop atTop :=
    tendsto_id.atTop_add tendsto_const_nhds
  have heq : (fun b : ℝ => b/(b+h)) =ᶠ[atTop] (fun b => 1-h/(b+h)) := by
    filter_upwards [hden.eventually (eventually_gt_atTop 0)] with b hb
    field_simp [ne_of_gt hb]
    ring
  apply Tendsto.congr' heq.symm
  simpa using (tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop hden) :
    Tendsto (fun b : ℝ => 1-h/(b+h)) atTop (nhds (1-0)))

lemma quantile_tendsto_atTop (μ : Measure ℝ≥0) [IsProbabilityMeasure μ]
    (h : ℝ) (hh : 0 < h)
    (hunbounded : ¬ ∃ M : ℝ≥0, expectedShortfall μ M = 0) :
    Tendsto (fun b : ℝ => (newsvendorLevel μ h b : ℝ)) atTop atTop := by
  apply tendsto_atTop.mpr
  intro r
  let M := Real.toNNReal r
  have hrM : r ≤ (M : ℝ) := Real.le_coe_toNNReal r
  have hCDF : μ.real (Set.Iic M) < 1 := by
    linarith only [tail_add_cdf μ M, tail_pos μ hunbounded M]
  have hevent : ∀ᶠ b : ℝ in atTop, μ.real (Set.Iic M) < b/(b+h) :=
    (fractile_tendsto h).eventually (eventually_gt_nhds hCDF)
  filter_upwards [hevent, eventually_gt_atTop (0 : ℝ)] with b hb hb0
  apply hrM.trans
  by_contra hnot
  have hQ : newsvendorLevel μ h b ≤ M :=
    NNReal.coe_le_coe.mp (le_of_not_ge hnot)
  have hmono : μ.real (Set.Iic (newsvendorLevel μ h b)) ≤ μ.real (Set.Iic M) :=
    measureReal_mono (Set.Iic_subset_Iic.mpr hQ)
  linarith only [quantile_cdf_lower μ h b hh hb0, hb, hmono]


lemma holding_ge_level_sub_mean (μ : Measure ℝ≥0) [IsProbabilityMeasure μ]
    (hmean : Integrable (fun d : ℝ≥0 => (d : ℝ)) μ) (S : ℝ≥0) :
    (S : ℝ) - (∫ d : ℝ≥0, (d : ℝ) ∂μ) ≤ expectedHolding μ S := by
  have hi : Integrable (fun d : ℝ≥0 => (S : ℝ) - (d : ℝ)) μ :=
    (integrable_const _).sub hmean
  calc
    _ = ∫ d : ℝ≥0, (S : ℝ) - (d : ℝ) ∂μ := by
      rw [integral_sub (integrable_const _) hmean]
      simp
    _ ≤ _ := integral_mono hi hi.pos_part (fun _ => le_max_left _ _)

lemma holding_eventually_pos (μ : Measure ℝ≥0) [IsProbabilityMeasure μ]
    (h : ℝ) (hh : 0 < h)
    (hmean : Integrable (fun d : ℝ≥0 => (d : ℝ)) μ)
    (hunbounded : ¬ ∃ M : ℝ≥0, expectedShortfall μ M = 0) :
    ∀ᶠ b : ℝ in atTop, 0 < expectedHolding μ (newsvendorLevel μ h b) := by
  have hQt := quantile_tendsto_atTop μ h hh hunbounded
  filter_upwards [hQt.eventually (eventually_gt_atTop (∫ d : ℝ≥0, (d : ℝ) ∂μ))] with b hb
  have hlow := holding_ge_level_sub_mean μ hmean (newsvendorLevel μ h b)
  linarith only [hb, hlow]

lemma ratio_bound (μ : Measure ℝ≥0) [IsProbabilityMeasure μ]
    (h b : ℝ) (hh : 0 < h) (hb : 0 < b)
    (hunbounded : ¬ ∃ M : ℝ≥0, expectedShortfall μ M = 0)
    (hQpos : 0 < (newsvendorLevel μ h b : ℝ))
    (hH : (newsvendorLevel μ h b : ℝ) / 2 ≤
      expectedHolding μ (newsvendorLevel μ h b)) :
    shortageHoldingRatio μ h b (newsvendorLevel μ h b) ≤
      2 * (meanResidualLife μ (newsvendorLevel μ h b) / (newsvendorLevel μ h b : ℝ)) := by
  let Q := newsvendorLevel μ h b
  let B := expectedShortfall μ Q
  let H := expectedHolding μ Q
  let t := μ.real (Set.Ioi Q)
  let m := meanResidualLife μ (Q : ℝ)
  have ht : 0 < t := tail_pos μ hunbounded Q
  have hB : 0 ≤ B := integral_nonneg fun _ => le_max_right _ _
  have hset : {d : ℝ≥0 | (Q : ℝ) < (d : ℝ)} = Set.Ioi Q := by
    ext d
    simp only [Set.mem_setOf_eq, Set.mem_Ioi, NNReal.coe_lt_coe]
  have hm : m = B / t := by
    dsimp only [m, meanResidualLife]
    have ht' : 0 < (μ (Set.Ioi Q)).toReal := ht
    rw [hset, if_pos ht']
    rfl
  have hm0 : 0 ≤ m := by rw [hm]; exact div_nonneg hB ht.le
  have hBt : B = t * m := by rw [hm]; field_simp [ne_of_gt ht]
  have htail : b * t ≤ h := by
    have hcdf := quantile_cdf_lower μ h b hh hb
    have hc := tail_add_cdf μ Q
    have hfrac : b / (b+h) ≤ 1-t := by
      dsimp only [Q, t] at hc ⊢
      linarith only [hcdf, hc]
    have hmul := (div_le_iff₀ (add_pos hb hh)).mp hfrac
    have hht : 0 ≤ h*t := mul_nonneg hh.le ht.le
    nlinarith only [hmul, hht]
  have hcharge : b * B ≤ h * m := by
    rw [hBt]
    nlinarith only [mul_le_mul_of_nonneg_right htail hm0]
  have hHpos : 0 < H := lt_of_lt_of_le (half_pos hQpos) hH
  change b * B / (h * H) ≤ 2 * (m / (Q : ℝ))
  calc
    _ ≤ (h * m) / (h * H) :=
      div_le_div_of_nonneg_right hcharge (mul_nonneg hh.le hHpos.le)
    _ = m / H := by field_simp [ne_of_gt hh, ne_of_gt hHpos]
    _ ≤ m / ((Q : ℝ) / 2) :=
      div_le_div_of_nonneg_left hm0 (half_pos hQpos) hH
    _ = 2 * (m / (Q : ℝ)) := by ring

lemma ratio_tendsto_zero_unbounded (μ : Measure ℝ≥0) [IsProbabilityMeasure μ]
    (h : ℝ) (hh : 0 < h)
    (hmean : Integrable (fun d : ℝ≥0 => (d : ℝ)) μ)
    (hassumption : AssumptionOne μ)
    (hunbounded : ¬ ∃ M : ℝ≥0, expectedShortfall μ M = 0) :
    Tendsto (fun b : ℝ => shortageHoldingRatio μ h b (newsvendorLevel μ h b))
      atTop (nhds 0) := by
  have hQt := quantile_tendsto_atTop μ h hh hunbounded
  have hlarge : ∀ᶠ b : ℝ in atTop,
      max (2 * ∫ d : ℝ≥0, (d : ℝ) ∂μ) 0 < (newsvendorLevel μ h b : ℝ) :=
    hQt.eventually (eventually_gt_atTop _)
  have hupp : ∀ᶠ b : ℝ in atTop,
      shortageHoldingRatio μ h b (newsvendorLevel μ h b) ≤
        2 * (meanResidualLife μ (newsvendorLevel μ h b) / (newsvendorLevel μ h b : ℝ)) := by
    filter_upwards [hlarge, eventually_gt_atTop (0 : ℝ)] with b hQ hb
    have hQ0 : 0 < (newsvendorLevel μ h b : ℝ) :=
      lt_of_le_of_lt (le_max_right _ _) hQ
    have hQmean : 2 * (∫ d : ℝ≥0, (d : ℝ) ∂μ) < (newsvendorLevel μ h b : ℝ) :=
      lt_of_le_of_lt (le_max_left _ _) hQ
    apply ratio_bound μ h b hh hb hunbounded hQ0
    have hlow := holding_ge_level_sub_mean μ hmean (newsvendorLevel μ h b)
    linarith only [hQmean, hlow]
  have hnonneg : ∀ᶠ b : ℝ in atTop,
      0 ≤ shortageHoldingRatio μ h b (newsvendorLevel μ h b) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with b hb
    exact div_nonneg
      (mul_nonneg hb (integral_nonneg fun _ => le_max_right _ _))
      (mul_nonneg hh.le (integral_nonneg fun _ => le_max_right _ _))
  have hlim : Tendsto
      (fun b : ℝ => 2 * (meanResidualLife μ (newsvendorLevel μ h b) /
        (newsvendorLevel μ h b : ℝ))) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul (hassumption.comp hQt) :
      Tendsto (fun b : ℝ => 2 * (meanResidualLife μ (newsvendorLevel μ h b) /
        (newsvendorLevel μ h b : ℝ))) atTop (nhds (2 * 0)))
  exact squeeze_zero' hnonneg hupp hlim

end LostSalesRatioUnbounded

namespace LostSalesMainAsymptotic

lemma factor_le (τ : ℕ) (h b q ε : ℝ) (hh : 0 < h) (hb : 1 ≤ b)
    (hq : 0 ≤ q) (hε : 0 < ε)
    (hsmall : ((1 + (τ : ℝ) * h) * ((τ : ℝ) + 1)) * q < ε) :
    (1 + ((b + (τ : ℝ) * h) * ((τ : ℝ) + 1) / b) * q) / (1 + q) ≤ 1 + ε := by
  have hb0 : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have hm : 0 ≤ (τ : ℝ) + 1 := by positivity
  have ha : 0 ≤ (τ : ℝ) * h := mul_nonneg (Nat.cast_nonneg _) hh.le
  have hba : (τ : ℝ) * h ≤ b * ((τ : ℝ) * h) := by nlinarith only [hb, ha]
  have hν : (b + (τ : ℝ) * h) * ((τ : ℝ) + 1) / b ≤
      (1 + (τ : ℝ) * h) * ((τ : ℝ) + 1) := by
    apply (div_le_iff₀ hb0).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hba hm]
  apply (div_le_iff₀ (show 0 < 1 + q by linarith only [hq])).mpr
  have hνq := mul_le_mul_of_nonneg_right hν hq
  have heq : 0 ≤ ε * q := mul_nonneg hε.le hq
  nlinarith only [hνq, hsmall, hq, heq]

lemma main_of_ratio_and_holding
    (P : CappedBaseStock.DemandLaw) (τ : ℕ) (h : ℝ) (hh : 0 < h)
    (hratio : Tendsto (fun b : ℝ => shortageHoldingRatio (leadTimeLaw P τ) h b
      (newsvendorLevel (leadTimeLaw P τ) h b)) atTop (nhds 0))
    (hhold : ∀ᶠ b in atTop, 0 < expectedHolding (leadTimeLaw P τ)
      (newsvendorLevel (leadTimeLaw P τ) h b))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ c : CappedBaseStock.Parameters,
        c.L = τ → c.h = h → b₀ ≤ c.p →
          (⨅ S : ℝ≥0, CappedBaseStock.baseStockCost P c S) ≤
            CappedBaseStock.baseStockCost P c
              (newsvendorLevel (leadTimeLaw P τ) h (c.p + (τ : ℝ) * h)) ∧
          CappedBaseStock.baseStockCost P c
              (newsvendorLevel (leadTimeLaw P τ) h (c.p + (τ : ℝ) * h)) ≤
            ENNReal.ofReal (1 + ε) * CappedBaseStock.OPT P c := by
  let ψ : ℝ → ℝ := fun b => shortageHoldingRatio (leadTimeLaw P τ) h (b / ((τ : ℝ) + 1))
    (newsvendorLevel (leadTimeLaw P τ) h (b / ((τ : ℝ) + 1)))
  have hscale : Tendsto (fun b : ℝ => b / ((τ : ℝ) + 1)) atTop atTop :=
    tendsto_id.atTop_div_const (by positivity)
  have hψ : Tendsto ψ atTop (nhds 0) := hratio.comp hscale
  let K : ℝ := (1 + (τ : ℝ) * h) * ((τ : ℝ) + 1)
  have hKψ : Tendsto (fun b => K * ψ b) atTop (nhds 0) := by
    simpa using hψ.const_mul K
  have hsmall : ∀ᶠ b in atTop, K * ψ b < ε :=
    hKψ.eventually (eventually_lt_nhds hε)
  have hholding : ∀ᶠ b in atTop, 0 < expectedHolding (leadTimeLaw P τ)
      (newsvendorLevel (leadTimeLaw P τ) h (b / ((τ : ℝ) + 1))) :=
    hscale.eventually hhold
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hsmall.and hholding)
  refine ⟨max 1 N, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro c hcL hch hcp
  have hcp1 : 1 ≤ c.p := (le_max_left _ _).trans hcp
  obtain ⟨hsmallc, hholdingc⟩ := hN c.p ((le_max_right _ _).trans hcp)
  have hholdingc' : 0 < expectedHolding (leadTimeLaw P c.L)
      (newsvendorLevel (leadTimeLaw P c.L) c.h (c.p / ((c.L : ℝ) + 1))) := by
    simpa only [hcL, hch] using hholdingc
  have hq : 0 ≤ ψ c.p := by
    apply div_nonneg
    · exact mul_nonneg (div_nonneg c.penalty_pos.le (by positivity))
        (integral_nonneg fun _ => le_max_right _ _)
    · exact mul_nonneg hh.le (integral_nonneg fun _ => le_max_right _ _)
  have hfactor := LostSalesMainAsymptotic.factor_le τ h c.p (ψ c.p) ε
    hh hcp1 hq hε hsmallc
  refine ⟨iInf_le _ _, ?_⟩
  have hfinite := theorem15a P c hholdingc'
  rw [hcL, hch] at hfinite
  exact hfinite.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hfactor) _)

end LostSalesMainAsymptotic

open LostSalesOrderUpTo.Asymptotic

/-- The multiplicative asymptotic guarantee also includes point-mass lead-time demand. -/
theorem solution
    (P : CappedBaseStock.DemandLaw) (τ : ℕ) (h : ℝ)
    (hτ : 1 ≤ τ) (hh : 0 < h)
    (hassumption : AssumptionOne (leadTimeLaw P τ)) :
    ∀ ε : ℝ, 0 < ε → ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ c : CappedBaseStock.Parameters,
        c.L = τ → c.h = h → b₀ ≤ c.p →
          (⨅ S : ℝ≥0, CappedBaseStock.baseStockCost P c S) ≤
            CappedBaseStock.baseStockCost P c
              (newsvendorLevel (leadTimeLaw P τ) h
                (c.p + (τ : ℝ) * h)) ∧
          CappedBaseStock.baseStockCost P c
              (newsvendorLevel (leadTimeLaw P τ) h
                (c.p + (τ : ℝ) * h)) ≤
            ENNReal.ofReal (1 + ε) * CappedBaseStock.OPT P c := by
  let μ : Measure ℝ≥0 := leadTimeLaw P τ
  let D : CappedBaseStock.DemandPath → ℝ≥0 :=
    fun d ↦ ∑ i ∈ Finset.range (τ + 1), d i
  have hD : Measurable D := by
    dsimp only [D]
    fun_prop
  letI : IsProbabilityMeasure μ := by
    change IsProbabilityMeasure ((CappedBaseStock.demandPathLaw P).map D)
    exact Measure.isProbabilityMeasure_map hD.aemeasurable
  have hmean : Integrable (fun d : ℝ≥0 ↦ (d : ℝ)) μ := by
    change Integrable (fun d : ℝ≥0 ↦ (d : ℝ))
      ((CappedBaseStock.demandPathLaw P).map D)
    apply (integrable_map_measure (g := fun d : ℝ≥0 ↦ (d : ℝ))
      (by fun_prop) hD.aemeasurable).2
    change Integrable (fun d : CappedBaseStock.DemandPath ↦
      ((∑ i ∈ Finset.range (τ + 1), d i : ℝ≥0) : ℝ))
      (CappedBaseStock.demandPathLaw P)
    simp only [NNReal.coe_sum]
    refine integrable_finsetSum _ (fun i _ ↦ ?_)
    have heval := measurePreserving_eval_infinitePi (fun _ : ℕ ↦ P.law) i
    exact heval.integrable_comp_of_integrable P.finiteMean
  intro ε hε
  by_cases hnonconstant : ¬ ∃ d : ℝ≥0, μ = Measure.dirac d
  · have hlimits :
        Tendsto (fun b : ℝ => shortageHoldingRatio μ h b (newsvendorLevel μ h b))
          atTop (nhds 0) ∧
        ∀ᶠ b in atTop, 0 < expectedHolding μ (newsvendorLevel μ h b) := by
      by_cases hbounded : ∃ M : ℝ≥0, expectedShortfall μ M = 0
      · exact RatioLimitAnalysis.ratio_and_holding_pos_of_bounded_demand
          μ h hh hmean hnonconstant hbounded
      · exact ⟨LostSalesRatioUnbounded.ratio_tendsto_zero_unbounded
          μ h hh hmean hassumption hbounded,
          LostSalesRatioUnbounded.holding_eventually_pos μ h hh hmean hbounded⟩
    exact LostSalesMainAsymptotic.main_of_ratio_and_holding P τ h hh
      hlimits.1 hlimits.2 ε hε
  · push_neg at hnonconstant
    obtain ⟨d, hd⟩ := hnonconstant
    refine ⟨1, zero_lt_one, ?_⟩
    intro c hcL hch _
    let b : ℝ := c.p + (τ : ℝ) * h
    let S : ℝ≥0 := newsvendorLevel μ h b
    have hb : 0 < b := add_pos_of_pos_of_nonneg c.penalty_pos
      (mul_nonneg (Nat.cast_nonneg _) hh.le)
    have hcost : backorderCost μ h b S ≤ 0 := by
      calc
        _ ≤ backorderCost μ h b d :=
          RatioLimitAnalysis.newsvendor_cost_le μ h b hh hb hmean d
        _ = 0 := by simp [hd, backorderCost, expectedHolding, expectedShortfall]
    refine ⟨iInf_le _ _, ?_⟩
    have hu := (lemma13 P c S).2
    rw [hcL, hch] at hu
    have hzero : CappedBaseStock.baseStockCost P c S ≤ 0 := by
      calc
        _ ≤ ENNReal.ofReal (backorderCost μ h b S) := hu
        _ ≤ 0 := by simpa using ENNReal.ofReal_le_ofReal hcost
    exact hzero.trans bot_le
