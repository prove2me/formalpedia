-- Prove2me | solution 1 for MixFlex.RiskNeutral.sf_objective_eq
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T09:58:30.186469+00:00
-- url     : https://prove2.me/submissions/9484a33f-c8f3-4aa0-9536-6ef0283b544f

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


theorem solution (P : Params) (hP : P.Standing) {N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → Fin N → ℝ) (Y : Ω → Fin (N + 1) → ℝ) (hS : Setting P μ X Y)
    (cF K : ℝ) (hK : 0 ≤ K) :
    vSF P μ X Y cF K =
      -(P.lam + (1 - P.lam) * P.theta) * cF * K
        + P.theta * P.p * ((∫ ω, (∑ n, X ω n) * (if ∑ n, X ω n ≤ K then 1 else 0) ∂μ)
          + K * (1 - μ.real {ω | ∑ n, X ω n ≤ K})) := by
  haveI := hS.prob
  rw [sf_integral P μ X Y hS cF K]
  have hm : Measurable (fun ω=>∑ n,X ω n) :=
    Finset.measurable_sum _ (fun n _=>(measurable_pi_apply n).comp hS.meas_X)
  have hi : Integrable (fun ω=>∑ n,X ω n) μ := integrable_finset_sum _ (fun n _=>hS.demand_int n)
  rw [min_integral μ _ hm hi K]


