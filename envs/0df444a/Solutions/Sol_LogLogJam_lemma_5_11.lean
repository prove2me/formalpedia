-- Prove2me | solution 1 for LogLogJam.lemma_5_11
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-26T09:13:21.676856+00:00
-- url     : https://prove2.me/submissions/65192ae0-0dad-4586-9908-907bffee1d24

import Mathlib
import Definitions.Def_LogLogJam_fisherInfo

open MeasureTheory LogLogJam
open scoped ENNReal

private theorem boundOnPeriod (p : ℝ → ℝ) (hC1 : ContDiff ℝ 1 p)
    (hnorm : ∫ y in (0 : ℝ)..Real.pi, p y = 1) (x : ℝ) (hx : x ∈ Set.Icc 0 Real.pi) :
    p x ≤ 1 / Real.pi + ∫ y in (0 : ℝ)..Real.pi, |deriv p y| := by
  have hp := Real.pi_pos
  let J := ∫ y in (0 : ℝ)..Real.pi, |deriv p y|
  have hd := hC1.continuous_deriv_one
  have osc (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ Real.pi) : |p b - p a| ≤ J := by
    rw [← intervalIntegral.integral_deriv_eq_sub (fun z _ => (hC1.differentiable_one z))
      (hd.intervalIntegrable a b)]
    exact (intervalIntegral.abs_integral_le_integral_abs hab).trans
      (intervalIntegral.integral_mono_interval ha hab hb
        (Filter.Eventually.of_forall fun z => abs_nonneg _) (hd.abs.intervalIntegrable _ _))
  have bound (y : ℝ) (hy : y ∈ Set.Icc 0 Real.pi) : p x - J ≤ p y := by
    rcases le_total y x with h|h
    · linarith [le_abs_self (p x - p y), osc y x hy.1 h hx.2]
    · linarith [neg_le_abs (p y - p x), osc x y hx.1 h hy.2]
  have h := intervalIntegral.integral_mono_on hp.le
    (intervalIntegrable_const (a := 0) (b := Real.pi) (μ := volume))
    (hC1.continuous.intervalIntegrable _ _) bound
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul, hnorm] at h
  have : p x - J ≤ 1 / Real.pi := (le_div_iff₀ hp).mpr (by linarith)
  linarith

theorem solution (p : ℝ → ℝ) (hpos : ∀ θ, 0 < p θ) (hper : ∀ θ, p (θ + Real.pi) = p θ)
    (hC1 : ContDiff ℝ 1 p) (hnorm : ∫ θ in Set.Ico 0 Real.pi, p θ = 1) (θ : ℝ) :
    ENNReal.ofReal (p θ) ≤ ENNReal.ofReal (1 / Real.pi) + (circFisher p) ^ (1 / 2 : ℝ) := by
  have hp := Real.pi_pos
  let f := fun x : ℝ => deriv p x ^ 2 / p x
  let J := ∫ x in (0 : ℝ)..Real.pi, |deriv p x|
  let F := ∫ x in (0 : ℝ)..Real.pi, f x
  have hc := hC1.continuous
  have hd := hC1.continuous_deriv_one
  have hf : Continuous f := (hd.pow 2).div hc (fun x => (hpos x).ne')
  have hfn x : 0 ≤ f x := div_nonneg (sq_nonneg _) (hpos x).le
  have hF : 0 ≤ F := intervalIntegral.integral_nonneg hp.le (fun x _ => hfn x)
  have hnorm' : ∫ y in (0 : ℝ)..Real.pi, p y = 1 := by
    rw [intervalIntegral.integral_of_le hp.le, ← integral_Ico_eq_integral_Ioc]; exact hnorm
  have hy (x : ℝ) : (2 * J) * |deriv p x| ≤ J^2 * p x + f x := by
    dsimp only [f]
    rw [← sub_le_iff_le_add']
    have H := sq_nonneg (J * p x - |deriv p x|)
    have he := sq_abs (deriv p x)
    apply (le_div_iff₀ (hpos x)).2
    nlinarith
  have hcs := intervalIntegral.integral_mono (μ := volume) hp.le
    ((continuous_const.mul hd.abs).intervalIntegrable 0 Real.pi)
    (((continuous_const.mul hc).add hf).intervalIntegrable 0 Real.pi) hy
  change (∫ x in (0 : ℝ)..Real.pi, (2 * J) * |deriv p x|) ≤
    ∫ x in (0 : ℝ)..Real.pi, J^2 * p x + f x at hcs
  rw [intervalIntegral.integral_add (f := fun x => J^2 * p x) (g := f)
    ((continuous_const.mul hc).intervalIntegrable _ _)
    (hf.intervalIntegrable _ _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, hnorm', mul_one] at hcs
  have hroot : J ≤ Real.sqrt F := Real.le_sqrt_of_sq_le (by change (2 * J) * J ≤ J ^ 2 + F at hcs; nlinarith)
  have hlog x : deriv (fun y => Real.log (p y)) x = deriv p x / p x :=
    (((hC1.differentiable_one x).hasDerivAt).log (hpos x).ne').deriv
  have idF : circFisher p = ENNReal.ofReal F := by
    dsimp only [circFisher, F]
    rw [intervalIntegral.integral_of_le hp.le, ← integral_Ico_eq_integral_Ioc,
      ofReal_integral_eq_lintegral_ofReal (hf.integrableOn_Icc.mono_set Set.Ico_subset_Icc_self)
        (Filter.Eventually.of_forall hfn)]
    apply lintegral_congr
    intro x
    rw [← ENNReal.ofReal_mul (hpos x).le, hlog]
    congr 1
    dsimp [f]
    field_simp [(hpos x).ne']
  let x := toIcoMod hp 0 θ
  have hx := toIcoMod_mem_Ico' hp θ
  have hpx : p x = p θ := Function.Periodic.sub_zsmul_eq (show Function.Periodic p Real.pi from hper) _
  have hb := boundOnPeriod p hC1 hnorm' x ⟨hx.1,hx.2.le⟩
  rw [hpx] at hb
  change p θ ≤ 1 / Real.pi + J at hb
  rw [idF, ENNReal.ofReal_rpow_of_nonneg hF (by norm_num), ← Real.sqrt_eq_rpow,
    ← ENNReal.ofReal_add (by positivity) (Real.sqrt_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (by linarith)
