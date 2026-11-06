-- Prove2me | solution 1 for LostSalesExpGap.ConstOrder.chernoff_step
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T07:06:56.804881+00:00
-- url     : https://prove2.me/submissions/94d5f8a5-5f61-45aa-b4df-8f5f7c37f6be

import Mathlib
import Definitions.Def_LostSalesExpGap_ConstOrder_ConstantOrder

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

open LostSalesExpGap.ConstOrder in
theorem solution (P : CappedBaseStock.DemandLaw) (c : CappedBaseStock.Parameters) :
    ∀ n : ℕ, 1 ≤ n →
      CappedBaseStock.demandPathLaw P
          {d | ∑ i ∈ Finset.range n, (d i : ℝ) ≤ (n : ℝ) * rInf P c} ≤
        ENNReal.ofReal (gamma P c ^ n) := by
  intro n hn
  set μ := CappedBaseStock.demandPathLaw P with hμ
  set r := rInf P c
  let X : ℕ → CappedBaseStock.DemandPath → ℝ := fun i d => (d i : ℝ)
  have hXm : ∀ i, Measurable (X i) := fun i =>
    by fun_prop
  have hind : iIndepFun X μ := by
    have := iIndepFun_infinitePi (P := fun _ : ℕ => P.law)
      (X := fun _ (x : ℝ≥0) => (x : ℝ)) (fun _ => by fun_prop)
    exact this
  -- the mgf of one coordinate
  have hmgf1 : ∀ i (t : ℝ), mgf (X i) μ t = ∫ x : ℝ≥0, Real.exp (t * (x : ℝ)) ∂P.law := by
    intro i t
    simp only [mgf, X]
    have hmap : μ.map (fun d : CappedBaseStock.DemandPath => d i) = P.law := by
      simp only [hμ, CappedBaseStock.demandPathLaw]
      exact Measure.infinitePi_map_eval _ i
    rw [← hmap, integral_map (measurable_pi_apply i).aemeasurable]
    exact (Measurable.aestronglyMeasurable (by fun_prop))
  set S : CappedBaseStock.DemandPath → ℝ := ∑ i ∈ Finset.range n, X i with hS
  have hSapp : ∀ d, S d = ∑ i ∈ Finset.range n, (d i : ℝ) := by
    intro d; simp [hS, X, Finset.sum_apply]
  have hset : {d : CappedBaseStock.DemandPath | ∑ i ∈ Finset.range n, (d i : ℝ) ≤ (n : ℝ) * r}
      = {d | S d ≤ (n : ℝ) * r} := by
    ext d; simp [hSapp]
  have hS0 : ∀ d, 0 ≤ S d := fun d => by rw [hSapp]; positivity
  -- Chernoff bound for each θ ≥ 0
  have key : ∀ θ : ℝ, 0 ≤ θ → μ.real {d | S d ≤ (n : ℝ) * r} ≤ phi P c θ ^ n := by
    intro θ hθ
    have hint : Integrable (fun d => Real.exp (-θ * S d)) μ := by
      refine Integrable.of_bound (C := 1) ?_ (ae_of_all _ fun d => ?_)
      · have : Measurable S := by
          rw [show S = fun d => ∑ i ∈ Finset.range n, (d i : ℝ) from funext hSapp]; fun_prop
        exact (Measurable.aestronglyMeasurable (by fun_prop))
      · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
        nlinarith [hS0 d]
    have h := measure_le_le_exp_mul_mgf (μ := μ) (X := S) ((n : ℝ) * r)
      (neg_nonpos.mpr hθ) hint
    have hsum : mgf S μ (-θ) = (∫ x : ℝ≥0, Real.exp (-θ * (x : ℝ)) ∂P.law) ^ n := by
      rw [hS, hind.mgf_sum hXm]
      simp_rw [hmgf1]
      rw [Finset.prod_const, Finset.card_range]
    rw [hsum] at h
    refine h.trans (le_of_eq ?_)
    simp only [phi, mul_pow, ← Real.exp_nat_mul]
    congr 1
    · congr 1; ring
  -- take n-th roots
  have hn0 : n ≠ 0 := by omega
  set q := μ.real {d | S d ≤ (n : ℝ) * r}
  have hq0 : 0 ≤ q := measureReal_nonneg
  have hphi0 : ∀ θ : ℝ, 0 ≤ θ → 0 ≤ phi P c θ := by
    intro θ _
    exact mul_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => (Real.exp_pos _).le)
  set q' := q ^ ((n : ℝ)⁻¹)
  have hq'0 : 0 ≤ q' := Real.rpow_nonneg hq0 _
  have hq'n : q' ^ n = q := Real.rpow_inv_natCast_pow hq0 hn0
  have hq'γ : q' ≤ gamma P c := by
    simp only [gamma]
    apply le_ciInf
    intro θ
    have := key θ θ.2
    rw [← hq'n] at this
    exact (pow_le_pow_iff_left₀ hq'0 (hphi0 θ θ.2) hn0).mp this
  have hfin : q ≤ gamma P c ^ n := by
    rw [← hq'n]; exact pow_le_pow_left₀ hq'0 hq'γ n
  rw [hset, ← ofReal_measureReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hfin
