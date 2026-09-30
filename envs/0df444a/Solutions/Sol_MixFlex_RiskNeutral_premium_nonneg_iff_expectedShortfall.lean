-- Prove2me | solution 1 for MixFlex.RiskNeutral.premium_nonneg_iff_expectedShortfall
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T10:00:21.708002+00:00
-- url     : https://prove2.me/submissions/b13b6f56-6399-48b6-9a06-684b200e3007

import Definitions.Def_MixFlex_RiskNeutral_Model
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.CDF
import Mathlib.Tactic
open MeasureTheory ProbabilityTheory Filter Set
open MixFlex.RiskNeutral
noncomputable section
open scoped Topology
attribute [local instance] Classical.propDecidable
private theorem bernoulli_integral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (B : Ω → ℝ) (hm : Measurable B)
    (h01 : ∀ᵐ ω ∂μ,B ω=0 ∨ B ω=1) :
    Integrable B μ ∧ (∫ ω,B ω ∂μ)=μ.real {ω|B ω=1} := by
  have hs : MeasurableSet {ω|B ω=1} := measurableSet_eq_fun hm measurable_const
  have heq : {ω|B ω=1}.indicator (fun _=> (1:ℝ)) =ᵐ[μ] B := by
    filter_upwards [h01] with ω h
    rcases h with h|h <;> simp [Set.indicator,h]
  constructor
  · exact ((integrable_const (μ:=μ) (1:ℝ)).indicator hs).congr heq
  · rw [← integral_congr_ae heq,integral_indicator_const _ hs]
    simp

private theorem profit_integral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (D B : Ω → ℝ) (hmD : Measurable D) (hiD : Integrable D μ)
    (hD : ∀ᵐ ω ∂μ,0≤D ω) (hmB : Measurable B)
    (h01 : ∀ᵐ ω ∂μ,B ω=0 ∨ B ω=1) (hind : IndepFun D B μ)
    (p c l K : ℝ) :
    Integrable (fun ω=>-(l+(1-l)*B ω)*c*K+p*min (D ω) (B ω*K)) μ ∧
    (∫ ω,-(l+(1-l)*B ω)*c*K+p*min (D ω) (B ω*K) ∂μ) =
    -(l+(1-l)*μ.real {ω|B ω=1})*c*K+
      μ.real {ω|B ω=1}*p*(∫ ω,min (D ω) K ∂μ) := by
  obtain ⟨hiB,hEB⟩ := bernoulli_integral μ B hmB h01
  have hiM : Integrable (fun ω=>min (D ω) K) μ := hiD.inf (integrable_const K)
  have hMi : IndepFun (fun ω=>min (D ω) K) B μ :=
    hind.comp (measurable_id.min measurable_const) measurable_id
  have hiP : Integrable (fun ω=>min (D ω) K*B ω) μ := hMi.integrable_mul hiM hiB
  have hE := hMi.integral_fun_mul_eq_mul_integral hiM.aestronglyMeasurable hiB.aestronglyMeasurable
  have hiC : Integrable (fun ω=>-(l+(1-l)*B ω)*c*K) μ :=
    (((integrable_const l).add (hiB.const_mul (1-l))).neg.mul_const c).mul_const K
  have heq : (fun ω=>-(l+(1-l)*B ω)*c*K+p*(min (D ω) K*B ω)) =ᵐ[μ]
      (fun ω=>-(l+(1-l)*B ω)*c*K+p*min (D ω) (B ω*K)) := by
    filter_upwards [h01,hD] with ω h hD
    rcases h with h|h <;> simp [h,min_eq_right hD]
  constructor
  · exact (hiC.add (hiP.const_mul p)).congr heq
  · rw [← integral_congr_ae heq,integral_add hiC (hiP.const_mul p),integral_const_mul,hE]
    rw [integral_mul_const,integral_mul_const,integral_neg,
      integral_add (integrable_const l) (hiB.const_mul (1-l)),integral_const,
      integral_const_mul,hEB]
    simp only [probReal_univ,one_smul]
    ring

private theorem sf_integral (P : Params) {N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → Fin N → ℝ) (Y : Ω → Fin (N+1) → ℝ) (hS : Setting P μ X Y)
    (c K : ℝ) : vSF P μ X Y c K = -(P.lam+(1-P.lam)*P.theta)*c*K+
      P.theta*P.p*(∫ ω,min (∑ n,X ω n) K ∂μ) := by
  haveI := hS.prob
  have hmx : Measurable (fun ω=>∑ n,X ω n) :=
    Finset.measurable_sum _ (fun n _=>(measurable_pi_apply n).comp hS.meas_X)
  have hix : Integrable (fun ω=>∑ n,X ω n) μ := integrable_finset_sum _ (fun n _=>hS.demand_int n)
  have hnx : ∀ᵐ ω ∂μ,0≤∑ n,X ω n := by
    filter_upwards [ae_all_iff.mpr hS.demand_nonneg] with ω h
    exact Finset.sum_nonneg (fun n _=>h n)
  have hmy := (measurable_pi_apply (Fin.last N)).comp hS.meas_Y
  have hind : IndepFun (fun ω=>∑ n,X ω n) (fun ω=>Y ω (Fin.last N)) μ :=
    hS.yield_demand_indep.comp (Finset.measurable_sum _ (fun n _=>measurable_pi_apply n))
      (measurable_pi_apply _)
  have h := (profit_integral μ _ _ hmx hix hnx hmy (hS.yield_01 _) hind P.p c P.lam K).2
  simpa only [Function.comp_apply,vSF,sfProfit,hS.yield_prob] using h

private theorem min_integral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (D : Ω → ℝ) (hm : Measurable D) (hi : Integrable D μ) (K : ℝ) :
    (∫ ω,min (D ω) K ∂μ) = (∫ ω,D ω*(if D ω≤K then 1 else 0) ∂μ)+
      K*(1-μ.real {ω|D ω≤K}) := by
  have hs : MeasurableSet {ω|D ω≤K} := measurableSet_le hm measurable_const
  have ht : Integrable (fun ω=>D ω*(if D ω≤K then 1 else 0)) μ := by
    convert! hi.indicator hs using 1
    funext ω; by_cases h : D ω≤K <;> simp [Set.indicator,h]
  have h1 : Integrable (fun ω=>if D ω≤K then (1:ℝ) else 0) μ := by
    convert! (integrable_const (μ:=μ) (1:ℝ)).indicator hs using 1
  have hval : (∫ ω,(if D ω≤K then (1:ℝ) else 0) ∂μ)=μ.real {ω|D ω≤K} := by
    simpa only [Set.indicator,Set.mem_setOf_eq,smul_eq_mul,mul_one] using
      (integral_indicator_const (μ:=μ) (1:ℝ) hs)
  have hrem : Integrable (fun ω=>1-(if D ω≤K then (1:ℝ) else 0)) μ :=
    (integrable_const 1).sub h1
  calc
    _ = ∫ ω,D ω*(if D ω≤K then 1 else 0)+K*(1-(if D ω≤K then 1 else 0)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with ω
      by_cases h : D ω≤K
      · simp [h,min_eq_left h]
      · simp [h,min_eq_right (le_of_not_ge h)]
    _ = _ := by
      rw [integral_add ht (hrem.const_mul K),integral_const_mul,
        integral_sub (integrable_const 1) h1,hval,integral_const]
      simp

private theorem dedicated_integral (P : Params) {N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → Fin N → ℝ) (Y : Ω → Fin (N+1) → ℝ) (hS : Setting P μ X Y)
    (n : Fin N) (K : ℝ) :
    Integrable (fun ω=>-(P.lam+(1-P.lam)*Y ω n.castSucc)*P.c*K+
      P.p*min (X ω n) (Y ω n.castSucc*K)) μ ∧
    (∫ ω,-(P.lam+(1-P.lam)*Y ω n.castSucc)*P.c*K+
      P.p*min (X ω n) (Y ω n.castSucc*K) ∂μ) =
    -(P.lam+(1-P.lam)*P.theta)*P.c*K+P.theta*P.p*(∫ ω,min (X ω n) K ∂μ) := by
  haveI := hS.prob
  have hmX : Measurable (fun ω=>X ω n) := (measurable_pi_apply n).comp hS.meas_X
  have hmY : Measurable (fun ω=>Y ω n.castSucc) := (measurable_pi_apply _).comp hS.meas_Y
  have hind : IndepFun (fun ω=>X ω n) (fun ω=>Y ω n.castSucc) μ :=
    hS.yield_demand_indep.comp (measurable_pi_apply n) (measurable_pi_apply _)
  simpa only [hS.yield_prob] using
    profit_integral μ _ _ hmX (hS.demand_int n) (hS.demand_nonneg n) hmY (hS.yield_01 _) hind
      P.p P.c P.lam K

private theorem sd_integral (P : Params) {N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → Fin N → ℝ) (Y : Ω → Fin (N+1) → ℝ) (hS : Setting P μ X Y)
    (K : Fin N → ℝ) : vSD P μ X Y K = ∑ n, (-(P.lam+(1-P.lam)*P.theta)*P.c*K n+
      P.theta*P.p*(∫ ω,min (X ω n) (K n) ∂μ)) := by
  unfold vSD sdProfit
  rw [integral_finset_sum _ (fun n _=>(dedicated_integral P μ X Y hS n (K n)).1)]
  exact Finset.sum_congr rfl (fun n _=>(dedicated_integral P μ X Y hS n (K n)).2)

private theorem newsvendor_optimal {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (D : Ω → ℝ) (hm : Measurable D) (hi : Integrable D μ)
    (c v q : ℝ) (hv : 0<v) (hq : μ.real {ω|D ω≤q}=1-c/v) :
    (∀ K : ℝ, -c*K+v*(∫ ω,min (D ω) K ∂μ) ≤ -c*q+v*(∫ ω,min (D ω) q ∂μ)) ∧
    -c*q+v*(∫ ω,min (D ω) q ∂μ) = v*(∫ ω,D ω*(if D ω≤q then 1 else 0) ∂μ) := by
  have hs : MeasurableSet {ω|D ω≤q} := measurableSet_le hm measurable_const
  have h1 : Integrable (fun ω=>if D ω≤q then (1:ℝ) else 0) μ := by
    convert! (integrable_const (μ:=μ) (1:ℝ)).indicator hs using 1
  have hval : (∫ ω,(if D ω≤q then (1:ℝ) else 0) ∂μ)=μ.real {ω|D ω≤q} := by
    simpa only [Set.indicator,Set.mem_setOf_eq,smul_eq_mul,mul_one] using
      (integral_indicator_const (μ:=μ) (1:ℝ) hs)
  have hrem : Integrable (fun ω=>1-(if D ω≤q then (1:ℝ) else 0)) μ :=
    (integrable_const 1).sub h1
  have hqmul : v*(1-μ.real {ω|D ω≤q})=c := by
    rw [hq]
    field_simp
    ring
  constructor
  · intro K
    have hiq : Integrable (fun ω=>min (D ω) q) μ := hi.inf (integrable_const q)
    have hiK : Integrable (fun ω=>min (D ω) K) μ := hi.inf (integrable_const K)
    have hp : ∀ ω,min (D ω) K ≤ min (D ω) q+(K-q)*(1-(if D ω≤q then 1 else 0)) := by
      intro ω
      by_cases h : D ω≤q
      · simpa [h,min_eq_left h] using (min_le_left (D ω) K)
      · simp only [h,ite_false,sub_zero,mul_one,min_eq_right (le_of_not_ge h)]
        linarith [min_le_right (D ω) K]
    have hh := integral_mono_ae hiK (hiq.add (hrem.const_mul (K-q))) (Eventually.of_forall hp)
    rw [integral_add' hiq (hrem.const_mul (K-q)),integral_const_mul,
      integral_sub (integrable_const 1) h1,hval,integral_const] at hh
    simp only [probReal_univ,one_smul] at hh
    have hh' := mul_le_mul_of_nonneg_left hh hv.le
    have hqK := congrArg (fun x=>x*K) hqmul
    have hqq := congrArg (fun x=>x*q) hqmul
    nlinarith
  · rw [min_integral μ D hm hi q]
    have hqq := congrArg (fun x=>x*q) hqmul
    nlinarith

private theorem sf_preferred (P : Params) (hP : P.Standing) {N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → Fin N → ℝ) (Y : Ω → Fin (N+1) → ℝ) (hS : Setting P μ X Y)
    (cF : ℝ) (hcF : cF≤P.c) : SFPreferred P μ X Y cF := by
  haveI := hS.prob
  intro K hK
  refine ⟨∑ n,K n,Finset.sum_nonneg (fun n _=>hK n),?_⟩
  have hs : Integrable (fun ω=>∑ n,X ω n) μ := integrable_finset_sum _ (fun n _=>hS.demand_int n)
  have hm (n : Fin N) : Integrable (fun ω=>min (X ω n) (K n)) μ :=
    (hS.demand_int n).inf (integrable_const _)
  have hmin : (∫ ω,∑ n,min (X ω n) (K n) ∂μ) ≤ (∫ ω,min (∑ n,X ω n) (∑ n,K n) ∂μ) := by
    apply integral_mono_ae (integrable_finset_sum _ (fun n _=>hm n)) (hs.inf (integrable_const _))
    filter_upwards [] with ω
    exact le_min (Finset.sum_le_sum (fun n _=>min_le_left _ _))
      (Finset.sum_le_sum (fun n _=>min_le_right _ _))
  rw [integral_finset_sum _ (fun n _=>hm n)] at hmin
  have hcoef : 0≤P.lam+(1-P.lam)*P.theta :=
    add_nonneg hP.lam_nonneg (mul_nonneg (sub_nonneg.mpr hP.lam_le_one) hP.theta_nonneg)
  have hcost := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcF hcoef)
    (show 0≤∑ n,K n from Finset.sum_nonneg (fun n _=>hK n))
  have hrev := mul_le_mul_of_nonneg_left hmin (mul_nonneg hP.theta_nonneg hP.p_pos.le)
  rw [sd_integral P μ X Y hS K,sf_integral P μ X Y hS cF (∑ n,K n),
    Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
  nlinarith


private theorem quantile_iff {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Z : Ω → ℝ) (hm : Measurable Z) (α : ℝ)
    (hα0 : 0 < α) (hα1 : α < 1) (t : ℝ) :
    lowerQuantile μ Z α ≤ t ↔ α ≤ μ.real {ω | Z ω ≤ t} := by
  haveI : IsProbabilityMeasure (μ.map Z) := μ.isProbabilityMeasure_map hm.aemeasurable
  let F := cdf (μ.map Z)
  have hf (y : ℝ) : F y = μ.real {ω | Z ω ≤ y} := by
    rw [cdf_eq_real]
    change ((μ.map Z) (Iic y)).toReal = (μ (Z ⁻¹' Iic y)).toReal
    rw [Measure.map_apply hm measurableSet_Iic]
  have heq : {y : ℝ | α ≤ μ.real {ω | Z ω ≤ y}} = {y : ℝ | α ≤ F y} := by
    ext y; simp only [Set.mem_setOf_eq, hf]
  let S := {y : ℝ | α ≤ F y}
  have hne : S.Nonempty := by
    obtain ⟨y, hy⟩ := ((tendsto_cdf_atTop (μ.map Z)).eventually (eventually_gt_nhds hα1)).exists
    exact ⟨y, hy.le⟩
  have hb : BddBelow S := by
    obtain ⟨y, hy⟩ := ((tendsto_cdf_atBot (μ.map Z)).eventually (eventually_lt_nhds hα0)).exists
    refine ⟨y, fun z hz => ?_⟩
    by_contra h
    have hh := F.mono (le_of_not_ge h)
    exact (not_lt_of_ge (hz.trans hh)) hy
  have hmem : α ≤ F (sInf S) := by
    have hlim : Tendsto F (𝓝[>] sInf S) (𝓝 (F (sInf S))) :=
      (F.right_continuous _).mono Ioi_subset_Ici_self
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with y hy
    obtain ⟨z, hz, hzy⟩ := exists_lt_of_csInf_lt hne hy
    exact hz.trans (F.mono hzy.le)
  rw [← hf, lowerQuantile, heq]
  exact ⟨fun h => hmem.trans (F.mono h), fun h => csInf_le hb h⟩

private theorem quantile_left {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Z : Ω → ℝ) (hm : Measurable Z) (α : ℝ)
    (hα0 : 0 < α) (hα1 : α < 1) :
    μ.real {ω | Z ω < lowerQuantile μ Z α} ≤ α := by
  haveI : IsProbabilityMeasure (μ.map Z) := μ.isProbabilityMeasure_map hm.aemeasurable
  let F := cdf (μ.map Z)
  let q := lowerQuantile μ Z α
  have hf (y : ℝ) : F y = μ.real {ω | Z ω ≤ y} := by
    rw [cdf_eq_real]
    change ((μ.map Z) (Iic y)).toReal = (μ (Z ⁻¹' Iic y)).toReal
    rw [Measure.map_apply hm measurableSet_Iic]
  have hlim := F.mono.tendsto_leftLim q
  have hl0 : 0 ≤ Function.leftLim F q := by
    apply ge_of_tendsto hlim
    exact Eventually.of_forall (fun t => cdf_nonneg _ _)
  have hl : Function.leftLim F q ≤ α := by
    apply le_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with t ht
    apply le_of_lt
    by_contra! h
    have hqt := (quantile_iff μ Z hm α hα0 hα1 t).mpr (by rwa [← hf])
    exact (not_lt_of_ge hqt) ht
  change (μ (Z ⁻¹' Iio q)).toReal ≤ α
  rw [← Measure.map_apply hm measurableSet_Iio,← measure_cdf (μ.map Z)]
  rw [StieltjesFunction.measure_Iio _ (tendsto_cdf_atBot _),sub_zero,
    ENNReal.toReal_ofReal hl0]
  exact hl

private theorem indicator_int {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (s : Set Ω) (hs : MeasurableSet s) :
    Integrable (fun ω => if ω∈s then (1:ℝ) else 0) μ ∧
    (∫ ω, (if ω∈s then (1:ℝ) else 0) ∂μ) = μ.real s := by
  constructor
  · convert! (integrable_const (μ:=μ) (1:ℝ)).indicator hs using 1
  · simpa only [Set.indicator,smul_eq_mul,mul_one] using
      (integral_indicator_const (μ:=μ) (1:ℝ) hs)

private theorem hinge_int {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Z : Ω → ℝ) (hm : Measurable Z) (hi : Integrable Z μ)
    (t : ℝ) :
    (∫ ω, max (t-Z ω) 0 ∂μ) = t*μ.real {ω|Z ω≤t} -
      (∫ ω,Z ω*(if Z ω≤t then 1 else 0) ∂μ) := by
  have hs : MeasurableSet {ω | Z ω≤t} := measurableSet_le hm measurable_const
  have ht : Integrable (fun ω => Z ω*(if Z ω≤t then 1 else 0)) μ := by
    convert! hi.indicator hs using 1
    funext ω
    by_cases h : Z ω≤t <;> simp [Set.indicator,h]
  obtain ⟨h1,hval⟩ := indicator_int μ {ω|Z ω≤t} hs
  simp only [Set.mem_setOf_eq] at h1 hval
  calc
    _ = ∫ ω,t*(if Z ω≤t then 1 else 0)-Z ω*(if Z ω≤t then 1 else 0) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with ω
      by_cases h : Z ω≤t
      · simp only [h,ite_true,mul_one,max_eq_left (sub_nonneg.mpr h)]
      · simp only [h,ite_false,mul_zero,sub_zero,max_eq_right (sub_nonpos.mpr (le_of_not_ge h))]
    _ = _ := by rw [integral_sub (h1.const_mul t) ht,integral_const_mul,hval]

private theorem es_hinge {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Z : Ω → ℝ) (hm : Measurable Z) (hi : Integrable Z μ)
    (α : ℝ) (hα0 : 0 < α) :
    expectedShortfall μ Z α = -lowerQuantile μ Z α +
      (∫ ω,max (lowerQuantile μ Z α-Z ω) 0 ∂μ)/α := by
  rw [hinge_int μ Z hm hi]
  unfold expectedShortfall
  field_simp
  ring

private theorem es_le_hinge {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Z : Ω → ℝ) (hm : Measurable Z) (hi : Integrable Z μ)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (t : ℝ) :
    expectedShortfall μ Z α ≤ -t+(∫ ω,max (t-Z ω) 0 ∂μ)/α := by
  let q := lowerQuantile μ Z α
  have hiq : Integrable (fun ω=>max (q-Z ω) 0) μ :=
    ((integrable_const q).sub hi).sup (integrable_const 0)
  have hit : Integrable (fun ω=>max (t-Z ω) 0) μ :=
    ((integrable_const t).sub hi).sup (integrable_const 0)
  rw [es_hinge μ Z hm hi α hα0]
  change -q+(∫ ω,max (q-Z ω) 0 ∂μ)/α ≤ -t+(∫ ω,max (t-Z ω) 0 ∂μ)/α
  by_cases hqt : q≤t
  · obtain ⟨h1,hval⟩ := indicator_int μ {ω|Z ω≤q} (measurableSet_le hm measurable_const)
    simp only [Set.mem_setOf_eq] at h1 hval
    have hp : ∀ ω, max (q-Z ω) 0+(t-q)*(if Z ω≤q then 1 else 0) ≤ max (t-Z ω) 0 := by
      intro ω
      simp only [max_def]
      split_ifs <;> linarith
    have hh := integral_mono_ae (hiq.add (h1.const_mul (t-q))) hit (Eventually.of_forall hp)
    rw [integral_add' hiq (h1.const_mul (t-q)),integral_const_mul,hval] at hh
    have hq := (quantile_iff μ Z hm α hα0 hα1 q).mp le_rfl
    have hm := mul_le_mul_of_nonneg_left hq (sub_nonneg.mpr hqt)
    apply (mul_le_mul_iff_right₀ hα0).mp
    field_simp
    nlinarith
  · obtain ⟨h1,hval⟩ := indicator_int μ {ω|Z ω<q} (measurableSet_lt hm measurable_const)
    simp only [Set.mem_setOf_eq] at h1 hval
    have hp : ∀ ω, max (q-Z ω) 0+(t-q)*(if Z ω<q then 1 else 0) ≤ max (t-Z ω) 0 := by
      intro ω
      simp only [max_def]
      split_ifs <;> linarith
    have hh := integral_mono_ae (hiq.add (h1.const_mul (t-q))) hit (Eventually.of_forall hp)
    rw [integral_add' hiq (h1.const_mul (t-q)),integral_const_mul,hval] at hh
    have hq := quantile_left μ Z hm α hα0 hα1
    have hm := mul_le_mul_of_nonpos_left hq (sub_nonpos.mpr (le_of_not_ge hqt))
    apply (mul_le_mul_iff_right₀ hα0).mp
    field_simp
    nlinarith

private theorem es_subadditive {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {N : ℕ} (Z : Fin N → Ω → ℝ) (hmeas : ∀ n, Measurable (Z n))
    (hint : ∀ n, Integrable (Z n) μ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    expectedShortfall μ (fun ω => ∑ n, Z n ω) α ≤ ∑ n, expectedShortfall μ (Z n) α := by
  let q : Fin N → ℝ := fun n=>lowerQuantile μ (Z n) α
  have hms : Measurable (fun ω=>∑ n,Z n ω) := Finset.measurable_sum _ (fun n _=>hmeas n)
  have his : Integrable (fun ω=>∑ n,Z n ω) μ := integrable_finset_sum _ (fun n _=>hint n)
  have hih (n : Fin N) : Integrable (fun ω=>max (q n-Z n ω) 0) μ :=
    ((integrable_const (q n)).sub (hint n)).sup (integrable_const 0)
  have hihs : Integrable (fun ω=>max ((∑ n,q n)-(∑ n,Z n ω)) 0) μ :=
    ((integrable_const _).sub his).sup (integrable_const 0)
  have hineq : (∫ ω,max ((∑ n,q n)-(∑ n,Z n ω)) 0 ∂μ) ≤
      ∑ n,∫ ω,max (q n-Z n ω) 0 ∂μ := by
    rw [← integral_finset_sum _ (fun n _=>hih n)]
    apply integral_mono_ae hihs (integrable_finset_sum _ (fun n _=>hih n))
    filter_upwards [] with ω
    apply max_le
    · rw [← Finset.sum_sub_distrib]
      exact Finset.sum_le_sum (fun n _=>le_max_left _ _)
    · exact Finset.sum_nonneg (fun n _=>le_max_right _ _)
  calc
    _ ≤ -(∑ n,q n)+(∫ ω,max ((∑ n,q n)-(∑ n,Z n ω)) 0 ∂μ)/α :=
      es_le_hinge μ _ hms his α hα0 hα1 _
    _ ≤ -(∑ n,q n)+(∑ n,∫ ω,max (q n-Z n ω) 0 ∂μ)/α := by gcongr
    _ = _ := by
      simp_rw [es_hinge μ _ (hmeas _) (hint _) α hα0]
      simp only [Finset.sum_add_distrib,Finset.sum_neg_distrib,Finset.sum_div]
      rfl

theorem solution (P : Params) (hP : P.Standing) {N : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → Fin N → ℝ) (Y : Ω → Fin (N + 1) → ℝ)
    (hS : Setting P μ X Y) (α : ℝ)
    (hα : α = 1 - (P.lam + (1 - P.lam) * P.theta) * P.c / (P.theta * P.p))
    (hα0 : 0 < α) (hα1 : α < 1) :
    SFPreferred P μ X Y P.c ↔
      0 ≤ α * ((∑ n, expectedShortfall μ (fun ω => X ω n) α)
        - expectedShortfall μ (fun ω => ∑ n, X ω n) α) := by
  haveI := hS.prob
  constructor
  · intro _
    exact mul_nonneg hα0.le (sub_nonneg.mpr (es_subadditive μ (fun n ω=>X ω n)
      (fun n=>(measurable_pi_apply n).comp hS.meas_X) hS.demand_int α hα0 hα1))
  · intro _
    exact sf_preferred P hP μ X Y hS P.c le_rfl


