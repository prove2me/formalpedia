-- Prove2me | solution 1 for MixFlex.RiskNeutral.investment_positive_iff
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T10:18:05.475299+00:00
-- url     : https://prove2.me/submissions/8ce97676-6d5e-4073-8736-4354306054d2

import Definitions.Def_MixFlex_RiskNeutral_Model
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.CDF
import Mathlib.Tactic
open MeasureTheory ProbabilityTheory Filter Set
open MixFlex.RiskNeutral
noncomputable section
open scoped Topology
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
    (hD : ∀ᵐ ω ∂μ,0≤ D ω) (hmB : Measurable B)
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
    (∫ ω,min (D ω) K ∂μ) = (∫ ω,D ω*(if D ω≤ K then 1 else 0) ∂μ)+
      K*(1-μ.real {ω|D ω≤ K}) := by
  have hs : MeasurableSet {ω|D ω≤ K} := measurableSet_le hm measurable_const
  have ht : Integrable (fun ω=>D ω*(if D ω≤ K then 1 else 0)) μ := by
    convert! hi.indicator hs using 1
    funext ω; by_cases h : D ω≤ K <;> simp [Set.indicator,h]
  have h1 : Integrable (fun ω=>if D ω≤ K then (1:ℝ) else 0) μ := by
    convert! (integrable_const (μ:=μ) (1:ℝ)).indicator hs using 1
  have hval : (∫ ω,(if D ω≤ K then (1:ℝ) else 0) ∂μ)=μ.real {ω|D ω≤ K} := by
    simpa only [Set.indicator,Set.mem_setOf_eq,smul_eq_mul,mul_one] using
      (integral_indicator_const (μ:=μ) (1:ℝ) hs)
  have hrem : Integrable (fun ω=>1-(if D ω≤ K then (1:ℝ) else 0)) μ :=
    (integrable_const 1).sub h1
  calc
    _ = ∫ ω,D ω*(if D ω≤ K then 1 else 0)+K*(1-(if D ω≤ K then 1 else 0)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with ω
      by_cases h : D ω≤ K
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
    (c v q : ℝ) (hv : 0<v) (hq : μ.real {ω|D ω≤ q}=1-c/v) :
    (∀ K : ℝ, -c*K+v*(∫ ω,min (D ω) K ∂μ) ≤ -c*q+v*(∫ ω,min (D ω) q ∂μ)) ∧
    -c*q+v*(∫ ω,min (D ω) q ∂μ) = v*(∫ ω,D ω*(if D ω≤ q then 1 else 0) ∂μ) := by
  have hs : MeasurableSet {ω|D ω≤ q} := measurableSet_le hm measurable_const
  have h1 : Integrable (fun ω=>if D ω≤ q then (1:ℝ) else 0) μ := by
    convert! (integrable_const (μ:=μ) (1:ℝ)).indicator hs using 1
  have hval : (∫ ω,(if D ω≤ q then (1:ℝ) else 0) ∂μ)=μ.real {ω|D ω≤ q} := by
    simpa only [Set.indicator,Set.mem_setOf_eq,smul_eq_mul,mul_one] using
      (integral_indicator_const (μ:=μ) (1:ℝ) hs)
  have hrem : Integrable (fun ω=>1-(if D ω≤ q then (1:ℝ) else 0)) μ :=
    (integrable_const 1).sub h1
  have hqmul : v*(1-μ.real {ω|D ω≤ q})=c := by
    rw [hq]
    field_simp
    ring
  constructor
  · intro K
    have hiq : Integrable (fun ω=>min (D ω) q) μ := hi.inf (integrable_const q)
    have hiK : Integrable (fun ω=>min (D ω) K) μ := hi.inf (integrable_const K)
    have hp : ∀ ω,min (D ω) K ≤ min (D ω) q+(K-q)*(1-(if D ω≤ q then 1 else 0)) := by
      intro ω
      by_cases h : D ω≤ q
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
    (cF : ℝ) (hcF : cF≤ P.c) : SFPreferred P μ X Y cF := by
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
  have hcoef : 0≤ P.lam+(1-P.lam)*P.theta :=
    add_nonneg hP.lam_nonneg (mul_nonneg (sub_nonneg.mpr hP.lam_le_one) hP.theta_nonneg)
  have hcost := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcF hcoef)
    (show 0≤∑ n,K n from Finset.sum_nonneg (fun n _=>hK n))
  have hrev := mul_le_mul_of_nonneg_left hmin (mul_nonneg hP.theta_nonneg hP.p_pos.le)
  rw [sd_integral P μ X Y hS K,sf_integral P μ X Y hS cF (∑ n,K n),
    Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
  nlinarith

private theorem cost_le_margin (P : Params) (hP : P.Standing)
    (ht : P.theta≤ P.lam*P.c/(P.p-(1-P.lam)*P.c)) :
    P.theta*P.p≤(P.lam+(1-P.lam)*P.theta)*P.c := by
  by_cases hd : 0<P.p-(1-P.lam)*P.c
  · have h := (le_div_iff₀ hd).mp ht
    nlinarith
  · have h := mul_nonpos_of_nonneg_of_nonpos hP.theta_nonneg (le_of_not_gt hd)
    have h' := mul_nonneg hP.lam_nonneg hP.c_pos.le
    nlinarith

private theorem profit_nonpos {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (D : Ω → ℝ) (hi : Integrable D μ) (c v K : ℝ)
    (hv : 0≤ v) (hc : v≤ c) (hK : 0≤ K) :
    -c*K+v*(∫ ω,min (D ω) K ∂μ)≤0 := by
  have h : (∫ ω,min (D ω) K ∂μ)≤ K := by
    calc
      _ ≤ ∫ ω,K ∂μ := integral_mono_ae (hi.inf (integrable_const K)) (integrable_const K)
        (Eventually.of_forall (fun _=>min_le_right _ _))
      _ = K := by simp
  have h1 := mul_le_mul_of_nonneg_left h hv
  have h2 := mul_le_mul_of_nonneg_right hc hK
  linarith

private theorem min_zero_integral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (D : Ω → ℝ) (hD : ∀ᵐ ω ∂μ,0≤ D ω) : (∫ ω,min (D ω) 0 ∂μ)=0 := by
  calc
    _ = ∫ ω,(0:ℝ) ∂μ := integral_congr_ae (hD.mono (fun ω h=>min_eq_right h))
    _ = 0 := integral_zero _ _

private theorem sd_zero (P : Params) {N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → Fin N → ℝ) (Y : Ω → Fin (N+1) → ℝ) (hS : Setting P μ X Y) :
    vSD P μ X Y (fun _=>0)=0 := by
  rw [sd_integral P μ X Y hS]
  simp only [mul_zero,zero_add,min_zero_integral μ _ (hS.demand_nonneg _),Finset.sum_const_zero]

private theorem low_investment (P : Params) (hP : P.Standing) {N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → Fin N → ℝ) (Y : Ω → Fin (N+1) → ℝ) (hS : Setting P μ X Y)
    (ht : P.theta≤ P.lam*P.c/(P.p-(1-P.lam)*P.c)) :
    (∀ K : ℝ,0≤ K→vSF P μ X Y P.c K≤0) ∧
    (∀ K : Fin N→ℝ,(∀ n,0≤ K n)→vSD P μ X Y K≤0) := by
  haveI := hS.prob
  have hc := cost_le_margin P hP ht
  have hv := mul_nonneg hP.theta_nonneg hP.p_pos.le
  constructor
  · intro K hK
    rw [sf_integral P μ X Y hS P.c K]
    simpa only [neg_mul] using profit_nonpos μ _ (integrable_finset_sum _ (fun n _=>hS.demand_int n))
      _ _ K hv hc hK
  · intro K hK
    rw [sd_integral P μ X Y hS K]
    apply Finset.sum_nonpos
    intro n hn
    simpa only [neg_mul] using profit_nonpos μ _ (hS.demand_int n) _ _ (K n) hv hc (hK n)

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


private theorem positive_investment {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (D : Ω → ℝ) (hm : Measurable D) (hi : Integrable D μ)
    (hD : ∀ᵐ ω ∂μ,0<D ω) (c v : ℝ) (hc : 0≤ c) (hcv : c<v) :
    ∃ K : ℝ,0<K ∧ 0< -c*K+v*(∫ ω,min (D ω) K ∂μ) := by
  have hv : 0<v := lt_of_le_of_lt hc hcv
  let α := (1-c/v)/2
  have hα0 : 0<α := by dsimp [α]; have := (div_lt_one hv).mpr hcv; linarith
  have hα1 : α<1 := by dsimp [α]; have := div_nonneg hc hv.le; linarith
  let q := lowerQuantile μ D α
  have hzero : μ.real {ω|D ω≤0}=0 := by
    have hz : μ {ω|D ω≤0}=0 := by simpa only [not_lt] using (ae_iff.mp hD)
    simp only [measureReal_def,hz,ENNReal.toReal_zero]
  have hq : 0<q := by
    by_contra! h
    have hh := (quantile_iff μ D hm α hα0 hα1 0).mp h
    rw [hzero] at hh
    linarith
  let K := q/2
  have hK : 0<K := by dsimp [K]; positivity
  have hF : μ.real {ω|D ω≤ K}<α := by
    by_contra! h
    have hh := (quantile_iff μ D hm α hα0 hα1 K).mpr h
    dsimp [K] at hh
    linarith
  have hs : MeasurableSet {ω|D ω≤ K} := measurableSet_le hm measurable_const
  have h1 : Integrable (fun ω=>if D ω≤ K then (1:ℝ) else 0) μ := by
    convert! (integrable_const (μ:=μ) (1:ℝ)).indicator hs using 1
  have hval : (∫ ω,(if D ω≤ K then (1:ℝ) else 0) ∂μ)=μ.real {ω|D ω≤ K} := by
    simpa only [Set.indicator,Set.mem_setOf_eq,smul_eq_mul,mul_one] using
      (integral_indicator_const (μ:=μ) (1:ℝ) hs)
  have hrem : Integrable (fun ω=>1-(if D ω≤ K then (1:ℝ) else 0)) μ :=
    (integrable_const 1).sub h1
  have hp : ∀ᵐ ω ∂μ,K*(1-(if D ω≤ K then 1 else 0))≤ min (D ω) K := by
    filter_upwards [hD] with ω hD
    by_cases h : D ω≤ K
    · simp only [h,ite_true,sub_self,mul_zero,min_eq_left h];exact hD.le
    · simp only [h,ite_false,sub_zero,mul_one,min_eq_right (le_of_not_ge h),le_refl]
  have hh := integral_mono_ae (hrem.const_mul K) (hi.inf (integrable_const K)) hp
  rw [integral_const_mul,integral_sub (integrable_const 1) h1,hval,integral_const] at hh
  simp only [probReal_univ,one_smul] at hh
  change K*(1-μ.real {ω|D ω≤ K}) ≤ (∫ ω,min (D ω) K ∂μ) at hh
  have hαv : 2*α*v=v-c := by dsimp [α];field_simp <;> ring
  have hFk := mul_lt_mul_of_pos_left hF (mul_pos hK hv)
  have hpos := mul_pos (sub_pos.mpr hcv) hK
  have hmul := mul_le_mul_of_nonneg_left hh hv.le
  refine ⟨K,hK,?_⟩
  have hαK := congrArg (fun x=>x*K) hαv
  nlinarith

private theorem sd_single (P : Params) {N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → Fin N → ℝ) (Y : Ω → Fin (N+1) → ℝ) (hS : Setting P μ X Y)
    (n : Fin N) (K : ℝ) : vSD P μ X Y (Pi.single n K) =
      -(P.lam+(1-P.lam)*P.theta)*P.c*K+P.theta*P.p*(∫ ω,min (X ω n) K ∂μ) := by
  classical
  rw [sd_integral P μ X Y hS]
  rw [Finset.sum_eq_single n]
  · simp
  · intro i hi hne
    simp only [Pi.single_eq_of_ne hne,mul_zero,zero_add,min_zero_integral μ _ (hS.demand_nonneg i)]
  · simp

theorem solution (P : Params) (hP : P.Standing) {N : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → Fin N → ℝ) (Y : Ω → Fin (N + 1) → ℝ)
    (hS : Setting P μ X Y) :
    (P.theta ≤ P.lam * P.c / (P.p - (1 - P.lam) * P.c) →
      (∀ K : ℝ, 0 ≤ K → vSF P μ X Y P.c K ≤ 0) ∧
      (∀ K : Fin N → ℝ, (∀ n, 0 ≤ K n) → vSD P μ X Y K ≤ 0)) ∧
    (P.lam * P.c / (P.p - (1 - P.lam) * P.c) < P.theta → (1 - P.lam) * P.c < P.p → 0 < N →
      (∀ n, μ.real {ω | 0 < X ω n} = 1) →
      (∃ K : ℝ, 0 < K ∧ 0 < vSF P μ X Y P.c K) ∧
      (∀ n : Fin N, ∃ Kn : ℝ, 0 < Kn ∧ 0 < vSD P μ X Y (Pi.single n Kn))) := by
  classical
  haveI := hS.prob
  constructor
  · exact low_investment P hP μ X Y hS
  · intro ht hp hN hpos
    let C := (P.lam+(1-P.lam)*P.theta)*P.c
    let v := P.theta*P.p
    have hC : 0≤ C := mul_nonneg
      (add_nonneg hP.lam_nonneg (mul_nonneg (sub_nonneg.mpr hP.lam_le_one) hP.theta_nonneg)) hP.c_pos.le
    have hCv : C<v := by
      have hh := (div_lt_iff₀ (sub_pos.mpr hp)).mp ht
      dsimp [C,v]
      nlinarith
    have hm (n : Fin N) : Measurable (fun ω=>X ω n) := (measurable_pi_apply n).comp hS.meas_X
    have ha (n : Fin N) : ∀ᵐ ω ∂μ,0<X ω n := by
      exact (mem_ae_iff_prob_eq_one (measurableSet_lt measurable_const (hm n))).mpr
        ((ENNReal.toReal_eq_one_iff _).mp (hpos n))
    have has : ∀ᵐ ω ∂μ,0<∑ n,X ω n := by
      filter_upwards [ae_all_iff.mpr hS.demand_nonneg,ha ⟨0,hN⟩] with ω hn hp
      exact lt_of_lt_of_le hp (Finset.single_le_sum (fun n _=>hn n) (Finset.mem_univ (⟨0,hN⟩ : Fin N)))
    constructor
    · obtain ⟨K,hK,hprofit⟩ := positive_investment μ (fun ω=>∑ n,X ω n)
        (Finset.measurable_sum _ (fun n _=>hm n))
        (integrable_finset_sum _ (fun n _=>hS.demand_int n)) has C v hC hCv
      refine ⟨K,hK,?_⟩
      rw [sf_integral P μ X Y hS P.c K]
      simpa only [C,v,neg_mul] using hprofit
    · intro n
      obtain ⟨K,hK,hprofit⟩ := positive_investment μ (fun ω=>X ω n) (hm n)
        (hS.demand_int n) (ha n) C v hC hCv
      refine ⟨K,hK,?_⟩
      rw [sd_single P μ X Y hS n K]
      simpa only [C,v,neg_mul] using hprofit


