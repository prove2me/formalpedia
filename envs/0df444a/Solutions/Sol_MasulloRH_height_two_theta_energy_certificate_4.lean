-- Prove2me | solution 4 for MasulloRH.height_two_theta_energy_certificate
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T14:08:00.20615+00:00
-- url     : https://prove2.me/submissions/ca3d60f4-39b3-4314-b26b-07d2380b16c4

import Theorems.Thm_MasulloRH_height_two_energy_bound_from_central_interval
import Theorems.Thm_MasulloRH_scalar_curvature_endpoint_bound
import Theorems.Thm_MasulloRH_height_two_surrogate_truncation_bound
import Theorems.Thm_MasulloRH_height_two_curvature_row_of_interval_check
import Theorems.Thm_MasulloRH_height_two_central_interval_checks
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open MeasureTheory Set MasulloRH MasulloRH.GaussianApproximation MasulloRH.HeightTwoCurvature
set_option autoImplicit false

private theorem smooth_surrogate (j : ℕ) : ContDiff ℝ 2 (surrogate j) := by
  have hs (b : Bool) : ContDiff ℝ 2 (thetaSix b) := by
    cases b <;> unfold thetaSix factor arg <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop
  unfold surrogate
  fun_prop (disch := aesop)

private theorem central_cap_total : (∑ j ∈ Finset.range 816, cap (144+j)) = 1285944 := by
  set_option maxRecDepth 20000 in
  set_option maxHeartbeats 4000000 in
  decide +kernel

theorem solution :
    Integrable (fun x : ℝ => Real.exp (2*(3/4)*x + 2*(11/48)*|x|) *
      ‖residual 2 HeightTwoWitness.coeffs HeightTwoWitness.shifts x‖^2) ∧
    energy (3/4) (11/48) (residual 2 HeightTwoWitness.coeffs HeightTwoWitness.shifts) < 1/96 := by
  let w (x : ℝ) := Real.exp (2*(3/4)*x + 2*(11/48)*|x|)
  let R := residual 2 HeightTwoWitness.coeffs HeightTwoWitness.shifts
  let F (x : ℝ) := w x * ‖R x‖^2
  obtain ⟨hint, ht⟩ := MasulloRH.height_two_energy_bound_from_central_interval
  refine ⟨hint, ?_⟩
  change energy (3/4) (11/48) R ≤ (∫ x : ℝ in Icc (-23/8) (7/2), F x) +
    13/800000000 + 1/10000000000 at ht
  have hstep (j : ℕ) : edge (j+1) - edge j = 1/128 := by
    simp [edge]
    ring
  have hw (x y : ℝ) (hxy : x ≤ y) : w x ≤ Real.exp (3/2*y + 11/24*|y|) := by
    apply Real.exp_le_exp.mpr
    have h := abs_add_le (x-y) y
    rw [sub_add_cancel, abs_of_nonpos (sub_nonpos.mpr hxy)] at h
    linarith
  have hcell (j : ℕ) (hj : 144 ≤ j) (hjR : j < 960) (x : ℝ) (hx : x ∈ Icc (edge j) (edge (j+1))) :
      F x ≤ (cap j : ℝ)/1000000 := by
    have h := List.all_eq_true.mp MasulloRH.height_two_central_interval_checks
      (j-144) (List.mem_range.mpr (by omega))
    have checked : MasulloRH.InteriorEvaluator.passes j = true := by
      simpa only [show 144+(j-144) = j by omega] using h
    obtain ⟨A,M,E,hM,hl,hr,hb,hc⟩ := MasulloRH.height_two_curvature_row_of_interval_check j checked
    have hs := smooth_surrogate j
    have hp := MasulloRH.scalar_curvature_endpoint_bound (surrogate j) (deriv (surrogate j))
      (deriv (deriv (surrogate j))) (edge j) (edge (j+1)) M A hM
      (fun u => (hs.differentiable (by decide) u).hasDerivAt)
      (fun u => (hs.differentiable_deriv_two u).hasDerivAt)
      (fun u hu => (hb u hu).1) hl hr x hx
    rw [hstep] at hp
    have hst := (MasulloRH.height_two_surrogate_truncation_bound j x).trans (hb x hx).2
    have hnorm : ‖R x‖ ≤ A + M/131072 + E := by
      have tri := norm_add_le (R x - (surrogate j x : ℂ)) (surrogate j x : ℂ)
      rw [sub_add_cancel, Complex.norm_real, Real.norm_eq_abs] at tri
      change ‖R x - (surrogate j x : ℂ)‖ ≤ E at hst
      linarith
    apply le_trans _ hc
    apply (mul_le_mul_of_nonneg_right (hw x _ hx.2) (sq_nonneg _)).trans
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hnorm 2) (Real.exp_pos _).le
  let e (j : ℕ) := edge (144+j)
  have h0 : e 0 = -23/8 := by norm_num [e,edge]
  have hJ : e 816 = 7/2 := by norm_num [e,edge]
  have hi : Integrable F := hint
  have hmain : (∫ x : ℝ in Icc (e 0) (e 816), F x) ≤
      ∑ j ∈ Finset.range 816, (1/128:ℝ) * ((cap (144+j) : ℝ)/1000000) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by rw [h0,hJ]; norm_num)]
    rw [← intervalIntegral.sum_integral_adjacent_intervals (fun _ _ => hi.intervalIntegrable)]
    apply Finset.sum_le_sum
    intro j hj
    have h : j < 816 := Finset.mem_range.mp hj
    have hs : e (j+1)-e j = 1/128 := by simpa only [e,Nat.add_assoc] using hstep (144+j)
    calc
      (∫ x in e j..e (j+1), F x) ≤ ∫ _ in e j..e (j+1), (cap (144+j):ℝ)/1000000 := by
        apply intervalIntegral.integral_mono_on (by linarith : e j ≤ e (j+1)) hi.intervalIntegrable intervalIntegrable_const
        intro x hx
        apply hcell (144+j) (by omega) (by omega) x
        simpa only [e,Nat.add_assoc] using hx
      _ = _ := by rw [intervalIntegral.integral_const,hs]; simp
  rw [h0,hJ] at hmain
  have hcast : (∑ j ∈ Finset.range 816, (cap (144+j) : ℝ)) = 1285944 := by
    exact_mod_cast central_cap_total
  have hin : (∑ j ∈ Finset.range 816, (1/128 : ℝ) * ((cap (144+j) : ℝ)/1000000)) =
      (1285944:ℝ)/128000000 := by
    simp_rw [div_eq_mul_inv, ← mul_assoc]
    rw [← Finset.sum_mul, ← Finset.mul_sum, hcast]
    norm_num
  rw [hin] at hmain
  change energy (3/4) (11/48) R < 1/96
  linarith
