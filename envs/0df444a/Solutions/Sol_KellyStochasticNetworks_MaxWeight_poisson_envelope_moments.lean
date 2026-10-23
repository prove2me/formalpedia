-- Prove2me | solution 1 for KellyStochasticNetworks.MaxWeight.poisson_envelope_moments
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T08:58:41.826576+00:00
-- url     : https://prove2.me/submissions/576bb096-a965-4aa1-a672-0dafecafe44a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_MaxWeight_Network

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal
open KellyStochasticNetworks.MaxWeight

theorem g79y_int (r : ℝ≥0) (f : ℕ → ℝ) (C K : ℝ) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hf : ∀ a, |f a| ≤ C * K ^ a) : Integrable f (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  have hs : Summable (fun a : ℕ => Real.exp (-r) * C * ((r : ℝ) * K) ^ a / (a.factorial : ℝ)) := by
    have := (Real.summable_pow_div_factorial ((r : ℝ) * K)).mul_left (Real.exp (-r) * C)
    refine this.congr fun a => ?_; ring
  refine Summable.of_nonneg_of_le (fun a => by positivity) (fun a => ?_) hs
  rw [Real.norm_eq_abs, mul_pow]
  have h1 := hf a
  have h2 : 0 ≤ Real.exp (-r) * (r : ℝ) ^ a / (a.factorial : ℝ) := by positivity
  calc Real.exp (-r) * (r : ℝ) ^ a / (a.factorial : ℝ) * |f a|
      ≤ Real.exp (-r) * (r : ℝ) ^ a / (a.factorial : ℝ) * (C * K ^ a) :=
        mul_le_mul_of_nonneg_left h1 h2
    _ = _ := by ring

/-- x^p ≤ exp(p x) for x ≥ 0, p ≥ 0 -/
theorem g79y_rpow_le (x p : ℝ) (hx : 0 ≤ x) (hp : 0 ≤ p) : x ^ p ≤ Real.exp (p * x) := by
  rcases hx.lt_or_eq with hx' | hx'
  · rw [Real.rpow_def_of_pos hx']
    apply Real.exp_le_exp.mpr
    have := Real.log_le_sub_one_of_pos hx'
    nlinarith
  · subst hx'
    rcases hp.lt_or_eq with hp' | hp'
    · rw [Real.zero_rpow hp'.ne']; exact (Real.exp_pos _).le
    · subst hp'; simp

theorem g79y_env (B a : ℕ) : 0 ≤ incrementEnvelope B a ∧ incrementEnvelope B a ≤ a + B := by
  unfold incrementEnvelope
  constructor
  · positivity
  · have : max a B ≤ a + B := max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
    exact_mod_cast this

/-- exponential bound for `(1 + env/K)^(α+1)` -/
theorem g79y_bound (B : ℕ) (α K : ℝ) (hα : 0 < α) (hK : 0 < K) (a : ℕ) :
    |(1 + incrementEnvelope B a / K) ^ (α + 1)| + 1 ≤
      (Real.exp ((α + 1) * (1 + B / K)) + 1) * (Real.exp ((α + 1) / K)) ^ a := by
  obtain ⟨h0, h1⟩ := g79y_env B a
  have hx : 0 ≤ 1 + incrementEnvelope B a / K := by positivity
  rw [abs_of_nonneg (Real.rpow_nonneg hx _)]
  have e1 := g79y_rpow_le _ (α + 1) hx (by linarith)
  have e2 : Real.exp ((α + 1) * (1 + incrementEnvelope B a / K)) ≤
      Real.exp ((α + 1) * (1 + B / K)) * (Real.exp ((α + 1) / K)) ^ a := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : incrementEnvelope B a / K ≤ (a + B) / K := div_le_div_of_nonneg_right h1 hK.le
    have : (α + 1) * (incrementEnvelope B a / K) ≤ (α + 1) * ((a + B) / K) :=
      mul_le_mul_of_nonneg_left this (by linarith)
    have e : (α + 1) * (1 + (a + B) / K) = (α + 1) * (1 + B / K) + a * ((α + 1) / K) := by
      field_simp; ring
    nlinarith
  have hpow : 1 ≤ (Real.exp ((α + 1) / K)) ^ a :=
    one_le_pow₀ (Real.one_le_exp (by positivity))
  nlinarith

theorem solution (lam : ℝ≥0) (B : ℕ) (α δ : ℝ)
    (hα : 0 < α) (hδ : 0 < δ) :
    (∀ p : ℝ, 0 ≤ p → Integrable (fun a : ℕ => incrementEnvelope B a ^ p)
      (poissonMeasure lam)) ∧
    (∀ K : ℝ, 0 < K → Integrable (fun a : ℕ =>
      if δ * K < incrementEnvelope B a then
        |(1 + incrementEnvelope B a / K) ^ (α + 1)| + 1 else 0)
      (poissonMeasure lam)) ∧
    Tendsto (poissonTailRemainder lam B α δ) atTop (𝓝 0) := by
  have hI : ∀ K : ℝ, 0 < K → Integrable (fun a : ℕ =>
      if δ * K < incrementEnvelope B a then
        |(1 + incrementEnvelope B a / K) ^ (α + 1)| + 1 else 0) (poissonMeasure lam) := by
    intro K hK
    refine g79y_int lam _ (Real.exp ((α + 1) * (1 + B / K)) + 1) (Real.exp ((α + 1) / K))
      (by positivity) (by positivity) fun a => ?_
    split_ifs
    · rw [abs_of_nonneg (by positivity)]; exact g79y_bound B α K hα hK a
    · rw [abs_zero]; positivity
  refine ⟨fun p hp => ?_, hI, ?_⟩
  · refine g79y_int lam _ (Real.exp (p * B)) (Real.exp p) (by positivity) (by positivity) fun a => ?_
    obtain ⟨h0, h1⟩ := g79y_env B a
    rw [abs_of_nonneg (Real.rpow_nonneg h0 _)]
    refine (g79y_rpow_le _ _ h0 hp).trans ?_
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  · -- dominated convergence
    unfold poissonTailRemainder
    have hb := hI 1 one_pos
    set bound : ℕ → ℝ := fun a => |(1 + incrementEnvelope B a / 1) ^ (α + 1)| + 1 with hbd
    have hbI : Integrable bound (poissonMeasure lam) := by
      refine g79y_int lam _ (Real.exp ((α + 1) * (1 + B / 1)) + 1) (Real.exp ((α + 1) / 1))
        (by positivity) (by positivity) fun a => ?_
      rw [abs_of_nonneg (by positivity)]; exact g79y_bound B α 1 hα one_pos a
    have hlim : Tendsto (fun K : ℝ => ∫ a, (if δ * K < incrementEnvelope B a then
        |(1 + incrementEnvelope B a / K) ^ (α + 1)| + 1 else 0) ∂poissonMeasure lam) atTop
        (𝓝 (∫ a : ℕ, (0 : ℝ) ∂poissonMeasure lam)) := by
      refine tendsto_integral_filter_of_dominated_convergence bound ?_ ?_ hbI ?_
      · exact Eventually.of_forall fun K => (Measurable.of_discrete).aestronglyMeasurable
      · filter_upwards [eventually_ge_atTop (1 : ℝ)] with K hK
        refine Eventually.of_forall fun a => ?_
        obtain ⟨h0, -⟩ := g79y_env B a
        split_ifs
        · have hx : 0 ≤ 1 + incrementEnvelope B a / K := by positivity
          rw [Real.norm_of_nonneg (by positivity), hbd]
          simp only [div_one]
          rw [abs_of_nonneg (Real.rpow_nonneg hx _), abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
          have : incrementEnvelope B a / K ≤ incrementEnvelope B a :=
            div_le_self h0 hK
          have := Real.rpow_le_rpow hx (by linarith : 1 + incrementEnvelope B a / K ≤ 1 + incrementEnvelope B a)
            (by linarith : (0:ℝ) ≤ α + 1)
          linarith
        · rw [norm_zero]; simp only [hbd]; positivity
      · refine Eventually.of_forall fun a => ?_
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_gt_atTop (incrementEnvelope B a / δ)] with K hK
        rw [if_neg]
        rw [not_lt]
        have := (div_lt_iff₀ hδ).mp hK
        linarith
    simpa using hlim
