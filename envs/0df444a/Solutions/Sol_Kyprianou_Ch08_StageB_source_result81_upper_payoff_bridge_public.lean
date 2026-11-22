-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_upper_payoff_bridge_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T23:14:56.226183+00:00
-- url     : https://prove2.me/submissions/5f4cff0f-fde5-4142-80d3-85393ee1b49c

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_positive_open_clock_eq_all_times
import Theorems.Thm_AvramDividend_Classical_chat03_exact_upperfirst_discount_integrand_measurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
open MeasureTheory ProbabilityTheory Filter Set Topology
open AvramDividend.Classical Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

private theorem upper_clock_eq_at
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} (D : Kyprianou.Ch08.SpectrallyNegativeModel Ω P)
    (A : SpectrallyNegativeLevy P F) {ω : Ω}
    (hω : ∀ t : ℝ≥0, A.X t ω = D.X t ω) (x a : ℝ) :
    (tauPlus (shifted D.X x) a ω : ℝ≥0∞) = twoSidedExitUpTime A (a - x) ω := by
  have hright : ∀ t : ℝ≥0, ContinuousWithinAt (fun s => x + A.X s ω) (Ici t) t := fun t =>
    continuous_const.continuousWithinAt.add (A.rightCont ω t)
  have hclock := source_result81_positive_open_clock_eq_all_times
    (fun s : ℝ≥0 => x + A.X s ω) (Ioi a) isOpen_Ioi hright
  have hEq (u : ℝ≥0) : A.X u ω = D.X u ω := hω u
  have hD (u : ℝ≥0) : a < x + D.X u ω ↔ a < x + A.X u ω := by rw [hEq u]
  have hA (u : ℝ≥0) : a < x + A.X u ω ↔ a - x < A.X u ω := by constructor <;> intro h <;> linarith
  change sInf {t : ℝ≥0∞ | ∃ u : ℝ≥0, 0 < u ∧ (u : ℝ≥0∞) = t ∧
      a < x + D.X u ω} =
    ⨅ (u : ℝ≥0) (_ : a - x < A.X u ω), (u : ℝ≥0∞)
  simpa only [mem_Ioi, hD, hA] using hclock

private theorem lower_clock_eq_at
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} (D : Kyprianou.Ch08.SpectrallyNegativeModel Ω P)
    (A : SpectrallyNegativeLevy P F) {ω : Ω}
    (hω : ∀ t : ℝ≥0, A.X t ω = D.X t ω) (x : ℝ) :
    (tauMinus (shifted D.X x) 0 ω : ℝ≥0∞) = twoSidedExitDownTime A (-x) ω := by
  have hright : ∀ t : ℝ≥0, ContinuousWithinAt (fun s => x + A.X s ω) (Ici t) t := fun t =>
    continuous_const.continuousWithinAt.add (A.rightCont ω t)
  have hclock := source_result81_positive_open_clock_eq_all_times
    (fun s : ℝ≥0 => x + A.X s ω) (Iio (0 : ℝ)) isOpen_Iio hright
  have hEq (u : ℝ≥0) : A.X u ω = D.X u ω := hω u
  have hD (u : ℝ≥0) : x + D.X u ω < 0 ↔ x + A.X u ω < 0 := by rw [hEq u]
  have hA (u : ℝ≥0) : x + A.X u ω < 0 ↔ A.X u ω < -x := by constructor <;> intro h <;> linarith
  change sInf {t : ℝ≥0∞ | ∃ u : ℝ≥0, 0 < u ∧ (u : ℝ≥0∞) = t ∧
      x + D.X u ω < 0} =
    ⨅ (u : ℝ≥0) (_ : A.X u ω < -x), (u : ℝ≥0∞)
  simpa only [mem_Iio, hD, hA] using hclock

private theorem upper_payoff_bridge_core
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (D : SpectrallyNegativeModel Ω P)
    {F : Filtration ℝ≥0 mΩ} (A : SpectrallyNegativeLevy P F)
    (hpaths : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, A.X t ω = D.X t ω) (q x a : ℝ) :
    upBeforeDownExpectation P D.X q x a = (twoSidedExitExpectation A q a x).toReal := by
  classical
  let U : Ω → ℝ≥0∞ := fun ω => twoSidedExitUpTime A (a - x) ω
  let L : Ω → ℝ≥0∞ := fun ω => twoSidedExitDownTime A (-x) ω
  let payoff : Ω → ℝ≥0∞ := fun ω =>
    if U ω < L ω then ENNReal.ofReal (Real.exp (-(q * (U ω).toReal))) else 0
  let realPayoff : Ω → ℝ := fun ω => (payoff ω).toReal
  have hpay_meas : Measurable payoff := by
    simpa only [payoff, U, L] using
      chat03_exact_upperfirst_discount_integrand_measurable A (-x) (a - x) q
  have hreal_meas : AEStronglyMeasurable realPayoff P :=
    hpay_meas.ennreal_toReal.aestronglyMeasurable
  have hreal_nonneg : ∀ᵐ ω ∂P, 0 ≤ realPayoff ω :=
    Eventually.of_forall fun ω => ENNReal.toReal_nonneg
  have hpay_ne_top : ∀ ω, payoff ω ≠ ⊤ := by
    intro ω; by_cases h : U ω < L ω <;> simp [payoff, h]
  have hofpay : (fun ω => ENNReal.ofReal (realPayoff ω)) = payoff := by
    funext ω; simp [realPayoff, ENNReal.ofReal_toReal (hpay_ne_top ω)]
  have hreal_lintegral :
      (∫ ω, realPayoff ω ∂P) = (∫⁻ ω, payoff ω ∂P).toReal := by
    simpa only [hofpay] using
      MeasureTheory.integral_eq_lintegral_of_nonneg_ae hreal_nonneg hreal_meas
  have hpoint : realPayoff =ᵐ[P]
      (fun ω => if tauPlus (shifted D.X x) a ω < tauMinus (shifted D.X x) 0 ω
        then discountedAt q (tauPlus (shifted D.X x) a ω) else 0) := by
    filter_upwards [hpaths] with ω hω
    have hU := upper_clock_eq_at D A hω x a
    have hL := lower_clock_eq_at D A hω x
    by_cases hUL : U ω < L ω
    · have hsrc : tauPlus (shifted D.X x) a ω < tauMinus (shifted D.X x) 0 ω := by
        have h := hUL; simp only [U, L, ← hU, ← hL] at h; exact h
      have htop : U ω ≠ ⊤ := by
        intro ht; rw [ht] at hUL; simp at hUL
      cases hUfin : U ω with
      | top => exact (htop hUfin).elim
      | coe t =>
          have hUcoe : (tauPlus (shifted D.X x) a ω : ℝ≥0∞) = (t : ℝ≥0∞) := by
            have h := hUfin; simp only [U] at h; rw [hU]; exact h
          simp [realPayoff, payoff, U, L, hUL, hsrc, discountedAt, hUfin,
            hUcoe, hL, apply_ite, ENNReal.toReal_ofReal (Real.exp_nonneg _)]
          split_ifs with hcond
          · intro hle
            exact False.elim ((not_lt_of_ge hle) hcond)
          · exact le_of_not_gt hcond
    · have hsrc : ¬ tauPlus (shifted D.X x) a ω < tauMinus (shifted D.X x) 0 ω := by
        intro h; apply hUL; simp only [U, L, ← hU, ← hL]; exact h
      simp [realPayoff, payoff, U, L, hUL, hsrc]
  calc
    upBeforeDownExpectation P D.X q x a = ∫ ω, realPayoff ω ∂P := by
      simpa only [upBeforeDownExpectation] using integral_congr_ae hpoint.symm
    _ = (∫⁻ ω, payoff ω ∂P).toReal := hreal_lintegral
    _ = (twoSidedExitExpectation A q a x).toReal := rfl

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (D : Kyprianou.Ch08.SpectrallyNegativeModel Ω P)
    {F : Filtration ℝ≥0 mΩ}
    (A : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hpaths : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, A.X t ω = D.X t ω)
    (q x a : ℝ) :
    upBeforeDownExpectation P D.X q x a = (twoSidedExitExpectation A q a x).toReal := by
  exact upper_payoff_bridge_core D A hpaths q x a
