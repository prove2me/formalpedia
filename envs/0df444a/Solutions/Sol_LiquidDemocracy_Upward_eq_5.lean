-- Prove2me | solution 1 for LiquidDemocracy.Upward.eq_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T11:15:49.450587+00:00
-- url     : https://prove2.me/submissions/0476abf9-8551-4b1f-b47f-e900639fc5b3

import Mathlib
import Definitions.Def_LiquidDemocracy_Upward_Urn

open MeasureTheory LiquidDemocracy.Upward

theorem LD_eq5_support (p : ℝ) (k : ℕ) (m : ℕ) :
    wChain p k m {w | m + 1 < w} = 0 := by
  induction m with
  | zero => simp [wChain]
  | succ m ih =>
    simp only [wChain]
    rw [Measure.bind_apply (MeasurableSet.of_discrete) (Measurable.of_discrete).aemeasurable]
    have hae : ∀ᵐ w0 ∂wChain p k m, w0 ≤ m + 1 := by
      rw [ae_iff]; simpa [not_le] using ih
    rw [lintegral_eq_zero_iff (Measurable.of_discrete)]
    filter_upwards [hae] with w0 hw0
    simp only [wStep, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Pi.zero_apply]
    rw [Measure.dirac_apply, Measure.dirac_apply]
    have e1 : ¬ (m + 1 + 1 < w0 + 1) := by omega
    have e2 : ¬ (m + 1 + 1 < w0) := by omega
    simp [Set.indicator, e1, e2]

theorem LD_eq5_mean (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) (k : ℕ) (hk : 1 ≤ k) (m : ℕ) :
    ∫⁻ w, (w : ENNReal) ∂(wChain p k m) =
      ENNReal.ofReal (∏ j ∈ Finset.range m, (1 + p / ((k : ℝ) + j))) := by
  induction m with
  | zero => simp [wChain]
  | succ m ih =>
    simp only [wChain]
    rw [Measure.lintegral_bind (Measurable.of_discrete).aemeasurable
      (Measurable.of_discrete).aemeasurable]
    have hae : ∀ᵐ w0 ∂wChain p k m, w0 ≤ m + 1 := by
      rw [ae_iff]; simpa [not_le] using LD_eq5_support p k m
    have ht : (0 : ℝ) < (k : ℝ) + m := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      positivity
    have key : ∀ᵐ w0 ∂wChain p k m,
        ∫⁻ w, (w : ENNReal) ∂(wStep p (k + m) w0) =
          ENNReal.ofReal (1 + p / ((k : ℝ) + m)) * (w0 : ENNReal) := by
      filter_upwards [hae] with w0 hw0
      have hw0' : (w0 : ℝ) ≤ (k : ℝ) + m := by
        have : (w0 : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast hw0
        have : (1 : ℝ) ≤ k := by exact_mod_cast hk
        linarith
      have h1 : 0 ≤ p * w0 / ((k + m : ℕ) : ℝ) := by
        have := hp.1.le; positivity
      have h2 : p * w0 / ((k + m : ℕ) : ℝ) ≤ 1 := by
        rw [div_le_one (by push_cast; exact ht)]
        push_cast
        nlinarith [hp.2, hp.1, (Nat.cast_nonneg w0 : (0 : ℝ) ≤ w0)]
      simp only [wStep]
      rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
        lintegral_dirac, lintegral_dirac]
      rw [show ((w0 + 1 : ℕ) : ENNReal) = ENNReal.ofReal ((w0 : ℝ) + 1) by
            rw [← ENNReal.ofReal_natCast]; push_cast; rfl,
        show ((w0 : ℕ) : ENNReal) = ENNReal.ofReal (w0 : ℝ) by rw [ENNReal.ofReal_natCast]]
      simp only [smul_eq_mul]
      rw [← ENNReal.ofReal_mul h1, ← ENNReal.ofReal_mul (by linarith),
        ← ENNReal.ofReal_add (by positivity) (by nlinarith),
        ← ENNReal.ofReal_mul (by have := hp.1.le; positivity)]
      congr 1
      push_cast
      field_simp
      ring
    rw [lintegral_congr_ae key, lintegral_const_mul _ (Measurable.of_discrete), ih,
      ← ENNReal.ofReal_mul (by have := hp.1.le; positivity), Finset.prod_range_succ, mul_comm]

theorem LD_eq5_gamma (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) (k : ℕ) (hk : 1 ≤ k) (m : ℕ) :
    ∏ j ∈ Finset.range m, (1 + p / ((k : ℝ) + j)) =
      Real.Gamma ((k + m : ℕ) + p) * Real.Gamma k / (Real.Gamma (p + k) * Real.Gamma (k + m : ℕ)) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  induction m with
  | zero =>
    simp only [Finset.range_zero, Finset.prod_empty, add_zero]
    have h1 : Real.Gamma (k : ℝ) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
    have h2 : Real.Gamma (p + k) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith [hp.1])).ne'
    rw [add_comm (k : ℝ) p]
    field_simp
  | succ m ih =>
    rw [Finset.prod_range_succ, ih]
    have hA : ((k + (m + 1) : ℕ) : ℝ) + p = ((k + m : ℕ) + p) + 1 := by push_cast; ring
    have hB : ((k + (m + 1) : ℕ) : ℝ) = ((k + m : ℕ) : ℝ) + 1 := by push_cast; ring
    have hpos1 : (0 : ℝ) < ((k + m : ℕ) : ℝ) := by push_cast; linarith [(m.cast_nonneg : (0:ℝ) ≤ m)]
    rw [hA, hB, Real.Gamma_add_one (by linarith [hp.1]), Real.Gamma_add_one hpos1.ne']
    have g1 : Real.Gamma (k : ℝ) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
    have g2 : Real.Gamma (p + k) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith [hp.1])).ne'
    have g3 : Real.Gamma ((k + m : ℕ) : ℝ) ≠ 0 := (Real.Gamma_pos_of_pos hpos1).ne'
    have hne : (k : ℝ) + m ≠ 0 := by linarith [(m.cast_nonneg : (0:ℝ) ≤ m)]
    push_cast at *
    field_simp

theorem solution (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) (k n : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    ∫ w, (w : ℝ) ∂(wLaw p k n) =
      Real.Gamma (n + p) * Real.Gamma k / (Real.Gamma (p + k) * Real.Gamma n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hkn
  simp only [wLaw, if_pos hkn, Nat.add_sub_cancel_left]
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun w => by positivity)
    (Measurable.of_discrete).aestronglyMeasurable]
  simp_rw [ENNReal.ofReal_natCast]
  rw [LD_eq5_mean p hp k hk m, ENNReal.toReal_ofReal (by
    apply Finset.prod_nonneg; intro j _; have := hp.1.le; positivity), LD_eq5_gamma p hp k hk m]
