-- Prove2me | solution 1 for MasulloRH.quarter_shift_gaussian_central_energy
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T00:14:02.714337+00:00
-- url     : https://prove2.me/submissions/a42d4b50-5291-4cfa-9e81-061294455c75

import Theorems.Thm_MasulloRH_quarter_shift_residual_sixth_derivative_cell_bound
import Theorems.Thm_MasulloRH_quarter_shift_gaussian_derivative_and_weight_tables
import Theorems.Thm_MasulloRH_quarter_shift_rational_energy_score
import Theorems.Thm_MasulloRH_central_interval_arithmetic_sound
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open MeasureTheory Set MasulloRH MasulloRH.ThetaDerivativeCertificate MasulloRH.GaussianApproximation
open MasulloRH.CentralInterval

private theorem point_bound (c b : ℝ) (hl : 1/2 ≤ c-b) (hr : c+b ≤ 1) (j : ℤ)
    (hj : -112 ≤ j) (hk : j < 112) (x : ℝ)
    (hx : x ∈ Icc (centerQ j:ℝ) (centerQ (j+1):ℝ)) :
    Real.exp (2*c*x+2*b*|x|)*‖err x‖^2 ≤ ((weightQ j*(capQ j)^2:ℚ):ℝ) := by
  let u : ℚ := centerQ (j+1)
  have hw : Real.exp (2*c*x+2*b*|x|) ≤ (weightQ j:ℝ) := by
    have hmax : 2*c*x+2*b*|x| ≤ (max u (2*u):ℝ) := by
      by_cases h : 0 ≤ x
      · rw [abs_of_nonneg h]
        apply le_trans _ (le_max_right ..)
        nlinarith only [mul_nonneg (sub_nonneg.mpr hr) h,hx.2]
      · rw [abs_of_nonpos (le_of_not_ge h)]
        apply le_trans _ (le_max_left ..)
        nlinarith only [mul_nonpos_of_nonneg_of_nonpos (show 0≤2*(c-b)-1 by linarith) (le_of_not_ge h),hx.2]
    have hw0 : (expPoint (max u (2*u))).2 ≤ weightQ j :=
      of_decide_eq_true (Bool.and_eq_true_iff.mp (MasulloRH.quarter_shift_gaussian_derivative_and_weight_tables j hj hk)).2
    have hx0 := (MasulloRH.central_interval_arithmetic_sound.exp_ok
      (MasulloRH.central_interval_arithmetic_sound.point_ok (max u (2*u)))).2
    apply (Real.exp_le_exp.mpr hmax).trans
    simpa only [Rat.cast_max,Rat.cast_mul,Rat.cast_ofNat] using hx0.trans (Rat.cast_le.mpr hw0)
  have h := MasulloRH.quarter_shift_residual_sixth_derivative_cell_bound j hj hk x hx
  push_cast
  exact mul_le_mul hw (pow_le_pow_left₀ (norm_nonneg _) h 2) (sq_nonneg _) ((Real.exp_pos _).le.trans hw)

theorem solution (c b : ℝ) (hl : 1/2 ≤ c-b) (hr : c+b ≤ 1)
    (hi : Integrable (fun x : ℝ => Real.exp (2*c*x+2*b*|x|)*‖err x‖^2)) :
    (∫ x : ℝ in Icc (-7) 7, Real.exp (2*c*x+2*b*|x|)*‖err x‖^2) ≤ 31/1000000000000 := by
  let F (x : ℝ) := Real.exp (2*c*x+2*b*|x|)*‖err x‖^2
  let e (n : ℕ) : ℝ := centerQ ((n:ℤ)-112)
  have h0 : e 0 = -7 := by norm_num [e,centerQ]
  have hJ : e 224 = 7 := by norm_num [e,centerQ]
  have hstep (n : ℕ) : e (n+1)-e n=1/16 := by dsimp [e,centerQ];push_cast;ring
  have hmain : (∫ x in Icc (e 0) (e 224), F x) ≤
      ∑ n ∈ Finset.range 224, (cellCost ((n:ℤ)-112):ℝ) := by
    rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le (by rw [h0,hJ];norm_num)]
    rw [←intervalIntegral.sum_integral_adjacent_intervals (fun _ _ => hi.intervalIntegrable)]
    apply Finset.sum_le_sum;intro n hn
    let j : ℤ := (n:ℤ)-112
    have hj : -112 ≤ j := by dsimp [j];omega
    have hk : j < 112 := by dsimp [j];have := Finset.mem_range.mp hn;omega
    have he : e (n+1)=(centerQ (j+1):ℝ) := by dsimp [e,j,centerQ];push_cast;ring
    calc (∫ x in e n..e (n+1), F x) ≤ ∫ _ in e n..e (n+1), ((weightQ j*(capQ j)^2:ℚ):ℝ) := by
           apply intervalIntegral.integral_mono_on (by linarith [hstep n]) hi.intervalIntegrable intervalIntegrable_const
           intro x hx;rw [he] at hx;exact point_bound c b hl hr j hj hk x hx
         _ = _ := by rw [intervalIntegral.integral_const,hstep];simp [cellCost,j];ring
  rw [h0,hJ] at hmain
  apply hmain.trans
  have hh : ((∑ n ∈ Finset.range 224, cellCost ((n:ℤ)-112):ℚ):ℝ) ≤ ((31/1000000000000:ℚ):ℝ) :=
    Rat.cast_le.mpr MasulloRH.quarter_shift_rational_energy_score
  push_cast at hh
  exact hh
