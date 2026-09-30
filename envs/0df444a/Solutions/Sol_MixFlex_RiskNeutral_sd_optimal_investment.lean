-- Prove2me | solution 1 for MixFlex.RiskNeutral.sd_optimal_investment
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T09:58:30.779105+00:00
-- url     : https://prove2.me/submissions/67cdc46a-bf5e-4e76-b099-ba87336a067e

import Definitions.Def_MixFlex_RiskNeutral_Model
import Mathlib.Probability.Independence.Integration
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

theorem solution (P : Params) (hP : P.Standing) {N : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → Fin N → ℝ) (Y : Ω → Fin (N + 1) → ℝ)
    (hS : Setting P μ X Y) (htheta : 0 < P.theta) (Kstar : Fin N → ℝ) (hK : ∀ n, 0 ≤ Kstar n)
    (hq : ∀ n, μ.real {ω | X ω n ≤ Kstar n}
      = 1 - (P.lam + (1 - P.lam) * P.theta) * P.c / (P.theta * P.p)) :
    (∀ K : Fin N → ℝ, (∀ n, 0 ≤ K n) → vSD P μ X Y K ≤ vSD P μ X Y Kstar) ∧
    vSD P μ X Y Kstar
      = P.theta * P.p * ∑ n, ∫ ω, X ω n * (if X ω n ≤ Kstar n then 1 else 0) ∂μ := by
  haveI := hS.prob
  have h (n : Fin N) := newsvendor_optimal μ (fun ω=>X ω n)
    ((measurable_pi_apply n).comp hS.meas_X) (hS.demand_int n)
    ((P.lam+(1-P.lam)*P.theta)*P.c) (P.theta*P.p) (Kstar n)
    (mul_pos htheta hP.p_pos) (hq n)
  constructor
  · intro K hK
    rw [sd_integral P μ X Y hS K,sd_integral P μ X Y hS Kstar]
    exact Finset.sum_le_sum (fun n _=>by simpa only [neg_mul] using (h n).1 (K n))
  · rw [sd_integral P μ X Y hS Kstar,Finset.mul_sum]
    exact Finset.sum_congr rfl (fun n _=>by simpa only [neg_mul] using (h n).2)


