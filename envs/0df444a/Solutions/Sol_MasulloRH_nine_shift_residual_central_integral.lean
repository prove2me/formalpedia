-- Prove2me | solution 1 for MasulloRH.nine_shift_residual_central_integral
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T21:49:07.237928+00:00
-- url     : https://prove2.me/submissions/663b5d8a-1159-4006-98df-9f9d7c838fa2

import Theorems.Thm_MasulloRH_nine_shift_interpolation_tables
import Theorems.Thm_MasulloRH_unit_gaussian_affine_enclosure_of_checked_intervals
import Theorems.Thm_MasulloRH_theta_grid_affine_enclosure_of_checked_intervals
import Theorems.Thm_MasulloRH_theta_norm_le_dyadic_on_tails
import Theorems.Thm_MasulloRH_central_interval_arithmetic_sound
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open MeasureTheory Set MasulloRH MasulloRH.NineShift MasulloRH.GaussianApproximation
open MasulloRH.CentralInterval

private theorem theta_all (j : ℤ) : Approx theta j (thetaRow j) := by
  by_cases h : -48 ≤ j ∧ j < 24
  · exact MasulloRH.theta_grid_affine_enclosure_of_checked_intervals _ _
      (MasulloRH.nine_shift_interpolation_tables.1 j h.1 h.2)
  · intro s h0 h1
    have ht : (grid j:ℝ)+s/16 ≤ -3 ∨ 3/2 ≤ (grid j:ℝ)+s/16 := by
      by_cases hj : j < -48
      · left;have hj' : (j:ℝ) ≤ -49 := by exact_mod_cast (show j ≤ -49 by omega)
        unfold grid;push_cast;linarith
      · right;have hj' : (24:ℝ) ≤ j := by exact_mod_cast (show 24 ≤ j by omega)
        unfold grid;push_cast;linarith
    have hθ := MasulloRH.theta_norm_le_dyadic_on_tails _ ht
    simp [thetaRow,h,line,value]
    exact hθ.trans (by norm_num)

private theorem convex_abs (l r s : ℝ) (hs : 0 ≤ s) (h1 : s ≤ 1) :
    |(1-s)*l+s*r| ≤ max |l| |r| := by
  apply (abs_add_le ..).trans
  rw [abs_mul,abs_mul,abs_of_nonneg (sub_nonneg.mpr h1),abs_of_nonneg hs]
  calc _ ≤ (1-s)*max |l| |r| + s*max |l| |r| := add_le_add
             (mul_le_mul_of_nonneg_left (le_max_left ..) (sub_nonneg.mpr h1))
             (mul_le_mul_of_nonneg_left (le_max_right ..) hs)
       _ = _ := by ring

private theorem cell_norm (j : ℤ) (hj : -96 ≤ j) (hk : j < 96)
    (s : ℝ) (hs : 0 ≤ s) (h1 : s ≤ 1) :
    ‖err ((grid j:ℝ)+s/16)‖ ≤ (capQ j:ℝ) := by
  let x : ℝ := (grid j:ℝ)+s/16
  let P := pulseRow j
  let T (i : Fin 9) := thetaRow (j-offset i)
  let a (i : Fin 9) : ℝ := coeff i
  let v (i : Fin 9) := theta (x-(shift i:ℝ))
  have ha (i : Fin 9) : 0 ≤ a i := by
    change 0 ≤ (coeff i : ℝ)
    exact_mod_cast (show ∀ i : Fin 9, 0 ≤ coeff i by decide +kernel) i
  have cast_a (i : Fin 9) : (a i:ℂ) = (coeff i:ℂ) := by simp [a]
  have hgrid (i : Fin 9) : x-(shift i:ℝ) = (grid (j-offset i):ℝ)+s/16 := by
    dsimp [x,shift,grid];push_cast;ring
  have hθ (i : Fin 9) : ‖v i - (line (T i) s:ℂ)‖ ≤ (value (T i).e:ℝ) := by
    dsimp only [v];rw [hgrid];exact theta_all _ s hs h1
  have hp := MasulloRH.unit_gaussian_affine_enclosure_of_checked_intervals j P
    (Bool.and_eq_true_iff.mp (MasulloRH.nine_shift_interpolation_tables.2.1 j hj hk)).1 s hs h1
  let z := ∑ i : Fin 9, (a i:ℂ)*(v i-(line (T i) s:ℂ))
  have hz : ‖z‖ ≤ ∑ i : Fin 9, a i*(value (T i).e:ℝ) := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum;intro i _
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (ha i)]
    exact mul_le_mul_of_nonneg_left (hθ i) (ha i)
  let L := line P s - ∑ i : Fin 9, a i * line (T i) s
  have hL : L = (1-s)*(net j Row.l:ℝ) + s*(net j Row.r:ℝ) := by
    have hlin : (∑ i : Fin 9, a i * line (T i) s) =
        (1-s)*(∑ i : Fin 9, a i*(value (T i).l:ℝ)) + s*(∑ i : Fin 9, a i*(value (T i).r:ℝ)) := by
      rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl;intro i _;unfold line;ring
    dsimp only [L];rw [hlin]
    dsimp only [line,P,a,T,net];push_cast;ring
  have hde : err x = ((pulse 0 x - (line P s:ℂ))-z) + (L:ℂ) := by
    dsimp only [err,GaussianApproximation.residual,z,L,v]
    simp only [Complex.ofReal_sub,Complex.ofReal_sum,Complex.ofReal_mul,cast_a,mul_sub,
      Finset.sum_sub_distrib]
    ring
  change ‖err x‖ ≤ _
  rw [hde]
  apply (norm_add_le _ _).trans
  have hrest := (norm_sub_le (pulse 0 x-(line P s:ℂ)) z).trans (add_le_add hp hz)
  rw [Complex.norm_real,Real.norm_eq_abs,hL]
  have hr : ((rad j:ℚ):ℝ) = (value P.e:ℝ) + ∑ i : Fin 9, a i * (value (T i).e:ℝ) := by
    simp [rad,P,T,a]
  unfold capQ;push_cast
  rw [hr];linarith only [hrest,convex_abs (net j Row.l:ℝ) (net j Row.r:ℝ) s hs h1]

private theorem point_bound (c b : ℝ) (hl : 1/2 ≤ c-b) (hr : c+b ≤ 1) (j : ℤ)
    (hj : -96 ≤ j) (hk : j < 96) (x : ℝ)
    (hx : x ∈ Icc (grid j:ℝ) (grid (j+1):ℝ)) :
    Real.exp (2*c*x+2*b*|x|)*‖err x‖^2 ≤ ((weightQ j*(capQ j)^2:ℚ):ℝ) := by
  let u : ℚ := grid (j+1)
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
      of_decide_eq_true (Bool.and_eq_true_iff.mp (MasulloRH.nine_shift_interpolation_tables.2.1 j hj hk)).2
    have hx0 := (MasulloRH.central_interval_arithmetic_sound.exp_ok
      (MasulloRH.central_interval_arithmetic_sound.point_ok (max u (2*u)))).2
    apply (Real.exp_le_exp.mpr hmax).trans
    simpa only [Rat.cast_max,Rat.cast_mul,Rat.cast_ofNat] using hx0.trans (Rat.cast_le.mpr hw0)
  have hstep : (grid (j+1):ℝ)=(grid j:ℝ)+1/16 := by unfold grid;push_cast;ring
  let s := 16*(x-(grid j:ℝ))
  have h0 : 0 ≤ s := by dsimp [s];linarith [hx.1]
  have h1 : s≤1 := by dsimp [s];linarith [hx.2]
  have heq : (grid j:ℝ)+s/16=x := by dsimp [s];ring
  have h := cell_norm j hj hk s h0 h1
  rw [heq] at h
  push_cast
  exact mul_le_mul hw (pow_le_pow_left₀ (norm_nonneg _) h 2) (sq_nonneg _) ((Real.exp_pos _).le.trans hw)

theorem solution (c b : ℝ) (hl : 1/2 ≤ c-b) (hr : c+b ≤ 1)
    (hi : Integrable (fun x : ℝ => Real.exp (2*c*x+2*b*|x|)*‖err x‖^2)) :
    (∫ x : ℝ in Icc (-6) 6, Real.exp (2*c*x+2*b*|x|)*‖err x‖^2) ≤ 59/1000000 := by
  let F (x : ℝ) := Real.exp (2*c*x+2*b*|x|)*‖err x‖^2
  let e (n : ℕ) : ℝ := grid ((n:ℤ)-96)
  have h0 : e 0 = -6 := by norm_num [e,grid]
  have hJ : e 192 = 6 := by norm_num [e,grid]
  have hstep (n : ℕ) : e (n+1)-e n=1/16 := by dsimp [e,grid];push_cast;ring
  have hmain : (∫ x in Icc (e 0) (e 192), F x) ≤
      ∑ n ∈ Finset.range 192, (cellCost ((n:ℤ)-96):ℝ) := by
    rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le (by rw [h0,hJ];norm_num)]
    rw [←intervalIntegral.sum_integral_adjacent_intervals (fun _ _ => hi.intervalIntegrable)]
    apply Finset.sum_le_sum;intro n hn
    let j : ℤ := (n:ℤ)-96
    have hj : -96 ≤ j := by dsimp [j];omega
    have hk : j < 96 := by dsimp [j];have := Finset.mem_range.mp hn;omega
    have he : e (n+1)=(grid (j+1):ℝ) := by dsimp [e,j,grid];push_cast;ring
    calc (∫ x in e n..e (n+1), F x) ≤ ∫ _ in e n..e (n+1), ((weightQ j*(capQ j)^2:ℚ):ℝ) := by
           apply intervalIntegral.integral_mono_on (by linarith [hstep n]) hi.intervalIntegrable intervalIntegrable_const
           intro x hx;rw [he] at hx;exact point_bound c b hl hr j hj hk x hx
         _ = _ := by rw [intervalIntegral.integral_const,hstep];simp [cellCost,j];ring
  rw [h0,hJ] at hmain
  apply hmain.trans
  have hh : ((∑ n ∈ Finset.range 192, cellCost ((n:ℤ)-96):ℚ):ℝ) ≤ ((59/1000000:ℚ):ℝ) :=
    Rat.cast_le.mpr MasulloRH.nine_shift_interpolation_tables.2.2
  push_cast at hh
  exact hh
