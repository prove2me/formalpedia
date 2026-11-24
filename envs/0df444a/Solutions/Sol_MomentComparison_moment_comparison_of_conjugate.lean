-- Prove2me | solution 1 for MomentComparison.moment_comparison_of_conjugate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:22:30.530848+00:00
-- url     : https://prove2.me/submissions/dfd1cc36-c3f4-4525-a70d-9755e78a8a7f

module
public import Definitions.Def_MomentComparison_Pairing
public import Definitions.Def_MomentComparison_Conformal
public import Definitions.Def_MomentComparison_Hypercontractivity
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Data.Real.ConjExponents
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Definitions.Def_MomentComparison_Basic
import all Definitions.Def_MomentComparison_Basic
public import Definitions.Def_MomentComparison_Upper
public import Theorems.Thm_MomentComparison_complexMomentNorm_interpolate
public import Theorems.Thm_MomentComparison_complexMomentNorm_pos
public import Theorems.Thm_MomentComparison_cubeAverage_const
public import Theorems.Thm_MomentComparison_cubeSign_mul_self
public import Theorems.Thm_MomentComparison_walsh_empty
attribute [local simp] MomentComparison.cubeAverage_const
attribute [local simp] MomentComparison.cubeSign_mul_self
attribute [local simp] MomentComparison.walsh_empty


section
public section
open scoped BigOperators
namespace MomentComparison
private theorem complexMomentNorm_real_one {n : ℕ} (f : Cube n → ℝ) :
    complexMomentNorm 1 (fun x => (f x : ℂ)) = cubeAverage (fun x => |f x|) := by
  simp only [complexMomentNorm, inv_one, Real.rpow_one, Complex.norm_real, Real.norm_eq_abs]
private theorem complexMomentNorm_real_two {n : ℕ} (f : Cube n → ℝ) :
    complexMomentNorm 2 (fun x => (f x : ℂ)) = Real.sqrt (cubeAverage fun x => f x ^ 2) := by
  simp only [complexMomentNorm, Real.rpow_two, Complex.norm_real, Real.norm_eq_abs,
    sq_abs, Real.sqrt_eq_rpow, one_div]
private theorem complexMomentNorm_interpolate' {n : ℕ} (f : Cube n → ℂ)
    {p r : ℝ} (hr1 : 1 < r) (hrp : r < p) :
    complexMomentNorm r f ≤
      complexMomentNorm 1 f ^ (1 - p * (r - 1) / (r * (p - 1))) *
      complexMomentNorm p f ^ (p * (r - 1) / (r * (p - 1))) := by
  have hp1 : 1 < p := hr1.trans hrp
  have hr : 0 < r := by linarith
  have hp : 0 < p := by linarith
  have hpm : 0 < p - 1 := sub_pos.mpr hp1
  let u := (r - 1) / (p - 1)
  have hu : 0 < u := div_pos (sub_pos.mpr hr1) hpm
  have hu' : u < 1 := (div_lt_one hpm).mpr (by linarith)
  have heq : r = (1 - u) + u * p := by
    dsimp [u]
    field_simp
    ring
  have h := complexMomentNorm_interpolate f hp hr hu hu' heq
  have hb : u * p / r = p * (r - 1) / (r * (p - 1)) := by
    dsimp [u]
    field_simp
  have ha : (1 - u) / r = 1 - p * (r - 1) / (r * (p - 1)) := by
    rw [← hb]
    apply (div_eq_iff hr.ne').mpr
    rw [sub_mul, one_mul, div_mul_cancel₀ _ hr.ne', heq]
    ring
  rwa [ha, hb] at h
end MomentComparison
end
end

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open MomentComparison
namespace MomentComparison
theorem _root_.solution {n d : ℕ} {p L : ℝ} (hp : 2 < p)
    (hL : 0 < L) (f : Cube n → ℝ)
    (hReverse : complexMomentNorm p (fun x => (f x : ℂ)) ≤
      L ^ d * complexMomentNorm (p / (p - 1)) (fun x => (f x : ℂ))) :
    Real.sqrt (cubeAverage fun x => f x ^ 2) ≤
      (L ^ (p / (2 * (p - 2)))) ^ d * cubeAverage (fun x => |f x|) := by
  let g : Cube n → ℂ := fun x => f x
  by_cases hg : ∃ x, g x ≠ 0
  · have hp1 : 1 < p := by linarith
    have hppos : 0 < p := by linarith
    have hpm1 : 0 < p - 1 := by linarith
    have hpm2 : 0 < p - 2 := by linarith
    let q := p / (p - 1)
    have hq1 : 1 < q := (lt_div_iff₀ hpm1).mpr (by linarith)
    have hqp : q < p := by
      apply (div_lt_iff₀ hpm1).mpr
      nlinarith [mul_pos hppos hpm2]
    let b := p / (2 * (p - 1))
    let c := 1 / (p - 1)
    let e := p / (2 * (p - 2))
    have hb : 0 < b := by dsimp [b]; positivity
    have hc : 0 < 1 - c := by
      dsimp [c]
      apply sub_pos.mpr
      exact (div_lt_one hpm1).mpr (by linarith)
    have he : 0 < e := by dsimp [e]; positivity
    have heq : e * (1 - c) = b := by
      dsimp [e, c, b]
      field_simp
      ring
    have h2 := complexMomentNorm_interpolate' g (r := 2) (p := p) (by norm_num) hp
    have hq := complexMomentNorm_interpolate' g hq1 hqp
    have hb' : p * ((2 : ℝ) - 1) / (2 * (p - 1)) = b := by norm_num [b]
    have hc' : p * (q - 1) / (q * (p - 1)) = c := by
      dsimp [q, c]
      field_simp
      ring
    rw [hb'] at h2
    rw [hc'] at hq
    have hA : 0 < complexMomentNorm 1 g := complexMomentNorm_pos _ hg
    have hB : 0 < complexMomentNorm p g := complexMomentNorm_pos _ hg
    have hTwo : 0 < complexMomentNorm 2 g := complexMomentNorm_pos _ hg
    have hQ : 0 < complexMomentNorm q g := complexMomentNorm_pos _ hg
    have h2Log := Real.log_le_log hTwo h2
    have hqLog := Real.log_le_log hQ hq
    have hReverseLog := Real.log_le_log hB hReverse
    change Real.log (complexMomentNorm p g) ≤ Real.log (L ^ d * complexMomentNorm q g)
      at hReverseLog
    rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hA _))
      (ne_of_gt (Real.rpow_pos_of_pos hB _)), Real.log_rpow hA, Real.log_rpow hB] at h2Log hqLog
    rw [Real.log_mul (pow_ne_zero _ hL.ne') hQ.ne', Real.log_pow] at hReverseLog
    have hGap : (1 - c) * (Real.log (complexMomentNorm p g) -
        Real.log (complexMomentNorm 1 g)) ≤ d * Real.log L := by
      linarith
    have hScaled := mul_le_mul_of_nonneg_left hGap he.le
    rw [← mul_assoc, heq] at hScaled
    have hFinal : Real.log (complexMomentNorm 2 g) ≤
        (d : ℝ) * (e * Real.log L) + Real.log (complexMomentNorm 1 g) := by
      linarith
    rw [← complexMomentNorm_real_one, ← complexMomentNorm_real_two]
    apply (Real.log_le_log_iff hTwo (mul_pos (pow_pos (Real.rpow_pos_of_pos hL _) _) hA)).mp
    rw [Real.log_mul (pow_ne_zero _ (Real.rpow_pos_of_pos hL e).ne') hA.ne',
      Real.log_pow, Real.log_rpow hL]
    simpa only [smul_eq_mul, mul_comm e (Real.log L)] using hFinal
  · push Not at hg
    have hf : f = 0 := by
      funext x
      exact Complex.ofReal_eq_zero.1 (hg x)
    simp [hf, cubeAverage]
end MomentComparison
