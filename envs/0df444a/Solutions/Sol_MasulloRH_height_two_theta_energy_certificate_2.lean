-- Prove2me | solution 2 for MasulloRH.height_two_theta_energy_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T12:37:22.474345+00:00
-- url     : https://prove2.me/submissions/ce66cc8f-3620-4b2e-a8e6-664a24f7cffe
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MasulloRH_height_two_outer_strip_density_bound
import Theorems.Thm_MasulloRH_scalar_curvature_endpoint_bound
import Theorems.Thm_MasulloRH_height_two_surrogate_truncation_bound
import Theorems.Thm_MasulloRH_height_two_curvature_row_bounds
import Theorems.Thm_MasulloRH_height_two_residual_exterior_bound
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

private theorem cap_total : (∑ j ∈ Finset.range 1024, cap j) = 1286152 := by
  set_option maxRecDepth 20000 in
  set_option maxHeartbeats 4000000 in
  decide +kernel

private theorem nonzero_cap : ∀ j : Fin 1024, 1 ≤ cap j.val := by
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
  obtain ⟨hint, _, ht⟩ := MasulloRH.height_two_residual_exterior_bound
  refine ⟨hint, ?_⟩
  change energy (3/4) (11/48) R - (∫ x : ℝ in Icc (-4) 4, F x) ≤ 1/10000000000 at ht
  have hstep (j : ℕ) : edge (j+1) - edge j = 1/128 := by
    simp [edge]
    ring
  have hinc (j : ℕ) : edge j ≤ edge (j+1) := by linarith [hstep j]
  have hw (x y : ℝ) (hxy : x ≤ y) : w x ≤ Real.exp (3/2*y + 11/24*|y|) := by
    apply Real.exp_le_exp.mpr
    have h := abs_add_le (x-y) y
    rw [sub_add_cancel, abs_of_nonpos (sub_nonpos.mpr hxy)] at h
    linarith
  have hcell (j : ℕ) (hj : j < 1024) (x : ℝ) (hx : x ∈ Icc (edge j) (edge (j+1))) :
      F x ≤ (cap j : ℝ)/1000000 := by
    by_cases hcj : 80 ≤ j ∧ j < 1008
    · obtain ⟨A,M,E,hM,hl,hr,hb,hc⟩ := MasulloRH.height_two_curvature_row_bounds j hcj.1 hcj.2
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
    · have hxl : -4 ≤ edge j := by
        unfold edge
        linarith [Nat.cast_nonneg (α := ℝ) j]
      have hxr : edge (j+1) ≤ 4 := by
        have : ((j+1:ℕ):ℝ) ≤ 1024 := by exact_mod_cast hj
        unfold edge
        linarith
      have hs : x ≤ -27/8 ∨ 31/8 ≤ x := by
        rcases lt_or_ge j 80 with h | h
        · left
          have ht : ((j+1:ℕ):ℝ) ≤ 80 := by exact_mod_cast h
          have hh := hx.2
          unfold edge at hh
          linarith
        · right
          have ht : (1008:ℝ) ≤ (j:ℝ) := by exact_mod_cast (show 1008 ≤ j by omega)
          have hh := hx.1
          unfold edge at hh
          linarith
      have ho := MasulloRH.height_two_outer_strip_density_bound x ⟨hxl.trans hx.1, hx.2.trans hxr⟩ hs
      have hcap : (1:ℝ) ≤ (cap j : ℝ) := by exact_mod_cast nonzero_cap ⟨j,hj⟩
      exact ho.trans (by linarith)
  have h0 : edge 0 = -4 := by norm_num [edge]
  have hJ : edge 1024 = 4 := by norm_num [edge]
  have hi : Integrable F := hint
  have hmain : (∫ x in Icc (edge 0) (edge 1024), F x) ≤
      ∑ j ∈ Finset.range 1024, (1/128 : ℝ) * ((cap j : ℝ)/1000000) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by rw [h0,hJ]; norm_num)]
    rw [← intervalIntegral.sum_integral_adjacent_intervals (fun _ _ => hi.intervalIntegrable)]
    apply Finset.sum_le_sum
    intro j hj
    calc
      (∫ x in edge j..edge (j+1), F x) ≤ ∫ _ in edge j..edge (j+1), (cap j : ℝ) / 1000000 :=
        intervalIntegral.integral_mono_on (hinc j) hi.intervalIntegrable intervalIntegrable_const
          (hcell j (Finset.mem_range.mp hj))
      _ = _ := by rw [intervalIntegral.integral_const, hstep]; simp
  rw [h0,hJ] at hmain
  have hcast : (∑ j ∈ Finset.range 1024, (cap j : ℝ)) = 1286152 := by
    exact_mod_cast cap_total
  have hin : (∑ j ∈ Finset.range 1024, (1/128 : ℝ) * ((cap j : ℝ)/1000000)) =
      (1286152 : ℝ)/128000000 := by
    simp_rw [div_eq_mul_inv, ← mul_assoc]
    rw [← Finset.sum_mul, ← Finset.mul_sum, hcast]
    norm_num
  rw [hin] at hmain
  change energy (3/4) (11/48) R < 1/96
  linarith
