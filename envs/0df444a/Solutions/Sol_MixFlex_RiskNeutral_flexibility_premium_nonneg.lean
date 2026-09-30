-- Prove2me | solution 1 for MixFlex.RiskNeutral.flexibility_premium_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T10:18:04.513007+00:00
-- url     : https://prove2.me/submissions/15088904-338b-456d-93c6-845b5c776ac3

import Definitions.Def_MixFlex_RiskNeutral_Model
import Mathlib.Probability.Independence.Integration
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic
open MeasureTheory ProbabilityTheory Filter Set
open MixFlex.RiskNeutral
noncomputable section
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

private theorem correlation_affine {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (U V : Ω → ℝ) (hU : MemLp U 2 μ) (hV : MemLp V 2 μ)
    (hvarU : 0 < variance U μ) (hvarV : 0 < variance V μ) (hρ : correlation μ U V = 1) :
    ∃ a b : ℝ, 0 < a ∧ V =ᵐ[μ] fun ω => a * U ω + b := by
  let c := Real.sqrt (variance U μ*variance V μ)
  have hc : 0 < c := Real.sqrt_pos.2 (mul_pos hvarU hvarV)
  have hc2 : c^2=variance U μ*variance V μ := Real.sq_sqrt (by positivity)
  have hcov : covariance U V μ = c := by
    change covariance U V μ / c = 1 at hρ
    exact (div_eq_one_iff_eq hc.ne').mp hρ
  let a := c/variance U μ
  have ha : 0 < a := div_pos hc hvarU
  have hm := hV.sub (hU.const_mul a)
  have hz : variance (fun ω => V ω-a*U ω) μ = 0 := by
    rw [variance_fun_sub hV (hU.const_mul a),covariance_const_mul_right,
      covariance_comm V U, hcov, variance_const_mul]
    dsimp [a]
    field_simp [hvarU.ne']
    nlinarith [hc2]
  refine ⟨a, ∫ ω, V ω-a*U ω ∂μ, ha, ?_⟩
  filter_upwards [ae_eq_integral_of_variance_eq_zero hm hz] with ω hω
  change V ω-a*U ω = (∫ x, V x-a*U x ∂μ) at hω
  linarith

private theorem affine_capacities {N : ℕ} (n0 : Fin N) (a b : Fin N→ℝ)
    (ha : ∀ n,0<a n) (K : ℝ) (hK : 0≤ K) :
    ∃ k : Fin N→ℝ,(∀ n,0≤ k n) ∧ (∑ n,k n)=K ∧
      ∀ u : ℝ,(∀ n,0≤ a n*u+b n)→
        (∑ n,min (a n*u+b n) (k n))=min (∑ n : Fin N, (a n*u+b n)) K := by
  let L := -(∑ n,|b n/a n|)-1
  have hL (n : Fin N) : a n*L+b n≤0 := by
    have hs : |b n/a n|≤∑ i,|b i/a i| :=
      Finset.single_le_sum (s:=Finset.univ) (f:=fun i : Fin N=>|b i/a i|) (fun i _=>abs_nonneg _) (Finset.mem_univ n)
    have hratio : L≤ -b n/a n := by
      have hh := le_abs_self (b n/a n)
      dsimp [L]
      rw [neg_div]
      linarith
    have hh := mul_le_mul_of_nonneg_left hratio (ha n).le
    have he : a n*(-b n/a n)= -b n := by field_simp [(ha _).ne'] <;> ring
    rw [he] at hh
    linarith
  let R := max L ((K-b n0)/a n0)
  have hLR : L≤ R := le_max_left _ _
  let F : ℝ→ℝ := fun t=>∑ n,max (a n*t+b n) 0
  have hFc : Continuous F := by
    apply continuous_finset_sum
    intro n hn
    exact ((continuous_const.mul continuous_id).add continuous_const).max continuous_const
  have hFL : F L=0 := by
    dsimp [F]
    simp only [max_eq_right (hL _),Finset.sum_const_zero]
  have hFR : K≤ F R := by
    have hR : (K-b n0)/a n0≤ R := le_max_right _ _
    have h0 := mul_le_mul_of_nonneg_left hR (ha n0).le
    have he : a n0*((K-b n0)/a n0)=K-b n0 := by field_simp [(ha _).ne'] <;> ring
    rw [he] at h0
    have hs : max (a n0*R+b n0) 0≤ F R :=
      Finset.single_le_sum (s:=Finset.univ) (f:=fun i : Fin N=>max (a i*R+b i) 0) (fun i _=>le_max_right _ _) (Finset.mem_univ n0)
    have hm := le_max_left (a n0*R+b n0) 0
    linarith
  obtain ⟨t,ht,hFt⟩ := intermediate_value_Icc hLR hFc.continuousOn (show K∈Icc (F L) (F R) from ⟨by rwa [hFL],hFR⟩)
  refine ⟨fun n=>max (a n*t+b n) 0,fun n=>le_max_right _ _,hFt,?_⟩
  intro u hu
  by_cases hut : u≤ t
  · have hle (n : Fin N) : a n*u+b n≤ max (a n*t+b n) 0 := by
      have h := mul_le_mul_of_nonneg_left hut (ha n).le
      have h' := le_max_left (a n*t+b n) 0
      linarith
    have hsum : (∑ n : Fin N, (a n*u+b n))≤ K := by
      rw [← hFt]
      exact Finset.sum_le_sum (fun n _=>hle n)
    simp only [min_eq_left (hle _),min_eq_left hsum]
  · have hle (n : Fin N) : max (a n*t+b n) 0≤ a n*u+b n := by
      have h := mul_le_mul_of_nonneg_left (le_of_not_ge hut) (ha n).le
      exact max_le (by linarith) (hu n)
    have hsum : K≤∑ n, (a n*u+b n) := by
      rw [← hFt]
      exact Finset.sum_le_sum (fun n _=>hle n)
    simp only [min_eq_right (hle _),min_eq_right hsum]
    exact hFt

private theorem perfect_preferred (P : Params) (hP : P.Standing) {N : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → Fin N → ℝ) (Y : Ω → Fin (N+1) → ℝ)
    (hS : Setting P μ X Y) (hi : ∀ n,MemLp (fun ω=>X ω n) 2 μ)
    (hv : ∀ n,0<variance (fun ω=>X ω n) μ)
    (hcor : ∀ m n,correlation μ (fun ω=>X ω m) (fun ω=>X ω n)=1) :
    SDPreferred P μ X Y P.c := by
  classical
  haveI := hS.prob
  by_cases hN : 0<N
  · let n0 : Fin N := ⟨0,hN⟩
    have hc (n : Fin N) := correlation_affine μ (fun ω=>X ω n0) (fun ω=>X ω n)
      (hi n0) (hi n) (hv n0) (hv n) (hcor n0 n)
    choose a b ha hab using hc
    intro K hK
    obtain ⟨k,hk,hks,hmatch⟩ := affine_capacities n0 a b ha K hK
    refine ⟨k,hk,?_⟩
    have hmatchAE : (fun ω=>∑ n,min (X ω n) (k n)) =ᵐ[μ]
        (fun ω=>min (∑ n,X ω n) K) := by
      filter_upwards [ae_all_iff.mpr hab,ae_all_iff.mpr hS.demand_nonneg] with ω he hn
      have hp (n : Fin N) : 0≤ a n*(X ω n0)+b n := by rw [← he n];exact hn n
      calc
        _ = ∑ n,min (a n*(X ω n0)+b n) (k n) :=
          Finset.sum_congr rfl (fun n _=>congrArg (fun x=>min x (k n)) (he n))
        _ = min (∑ n, (a n*(X ω n0)+b n)) K := hmatch (X ω n0) hp
        _ = _ := congrArg (fun x=>min x K) (Finset.sum_congr rfl (fun n _=>(he n).symm))
    have him (n : Fin N) : Integrable (fun ω=>min (X ω n) (k n)) μ :=
      (hS.demand_int n).inf (integrable_const (k n))
    rw [sf_integral P μ X Y hS P.c K,sd_integral P μ X Y hS k,
      Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,hks,
      ← integral_finset_sum Finset.univ (fun n _=>him n),
      integral_congr_ae hmatchAE]
  · have hN0 : N=0 := Nat.eq_zero_of_not_pos hN
    subst N
    intro K hK
    refine ⟨fun _=>0,fun _=>le_rfl,?_⟩
    rw [sd_zero P μ X Y hS,sf_integral P μ X Y hS P.c K]
    have hc : 0≤ P.lam+(1-P.lam)*P.theta :=
      add_nonneg hP.lam_nonneg (mul_nonneg (sub_nonneg.mpr hP.lam_le_one) hP.theta_nonneg)
    simp only [Fin.sum_univ_zero,min_eq_left hK,integral_zero,mul_zero,add_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc) hP.c_pos.le) hK

theorem solution (P : Params) (hP : P.Standing) {N : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → Fin N → ℝ) (Y : Ω → Fin (N + 1) → ℝ)
    (hS : Setting P μ X Y) :
    PremiumNonneg P μ X Y ∧
    (P.theta ≤ P.lam * P.c / (P.p - (1 - P.lam) * P.c) → PremiumZero P μ X Y) ∧
    ((∀ n, MemLp (fun ω => X ω n) 2 μ) → (∀ n, 0 < variance (fun ω => X ω n) μ) →
      (∀ m n, correlation μ (fun ω => X ω m) (fun ω => X ω n) = 1) → PremiumZero P μ X Y) := by
  refine ⟨fun cF hcF=>sf_preferred P hP μ X Y hS cF hcF,?_,?_⟩
  · intro ht
    refine ⟨sf_preferred P hP μ X Y hS P.c le_rfl,?_⟩
    intro K hK
    refine ⟨fun _=>0,fun _=>le_rfl,?_⟩
    rw [sd_zero P μ X Y hS]
    exact (low_investment P hP μ X Y hS ht).1 K hK
  · intro hi hv hc
    exact ⟨sf_preferred P hP μ X Y hS P.c le_rfl,perfect_preferred P hP μ X Y hS hi hv hc⟩


