-- Prove2me | solution 1 for MasulloRH.fixed_lattice_theta_gaussian_energy_gap
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T22:31:23.36519+00:00
-- url     : https://prove2.me/submissions/70bb6d3f-0e5a-47bf-ae85-ff6b77cad135

import Theorems.Thm_MasulloRH_unit_gaussian_theta_mellin_vertical_shift_separation
import Theorems.Thm_MasulloRH_exact_laplace_transform_of_gaussian_theta_residual
import Theorems.Thm_MasulloRH_exact_laplace_energy_bound_on_window
import Theorems.Thm_MasulloRH_finite_theta_approximation_excludes_rectangle_zeros
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open MeasureTheory MasulloRH.RationalThetaGrid MasulloRH.GaussianApproximation

private lemma repeat_phase {h : ℝ} (hh : 0 < h) (a : ℝ) (k : ℤ) :
    Complex.exp (vertical (2*Real.pi/h)*((a+h*(k:ℝ):ℝ):ℂ)) =
      Complex.exp (vertical (2*Real.pi/h)*(a:ℂ)) := by
  have hn : (h:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh.ne'
  have split : vertical (2*Real.pi/h)*((a+h*(k:ℝ):ℝ):ℂ) =
      vertical (2*Real.pi/h)*(a:ℂ)+(k:ℂ)*(2*(Real.pi:ℂ)*Complex.I) := by
    unfold vertical
    push_cast
    field_simp
  rw [split,Complex.exp_add,Complex.exp_int_mul_two_pi_mul_I,mul_one]

theorem solution (c b h a : ℝ) (hb : 0 < b) (hl : 0 < c-b) (hr : c+b < 1)
    (hh : 0 < h) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (m : ℕ) (v : Fin m → ℂ) (k : Fin m → ℤ),
      δ ≤ energy c b (residual 0 v (fun i => a+h*(k i:ℝ))) := by
  let t := 2*Real.pi/h
  let z := Complex.exp (vertical t*(a:ℂ))
  obtain ⟨s,hs,hd⟩ := MasulloRH.unit_gaussian_theta_mellin_vertical_shift_separation
    c b t hb (div_pos (mul_pos (by norm_num) Real.pi_pos) hh) z (Complex.exp_ne_zero _)
  let w := s+vertical t
  have hre : w.re = s.re := by simp [w,vertical]
  have hw : |w.re-c| < b := hre ▸ hs
  have h0 : 0 < s.re := by linarith [(abs_lt.mp hs).1]
  have h1 : s.re < 1 := by linarith [(abs_lt.mp hs).2]
  let C := 1/(2*(b-(s.re-c))) + 1/(2*(b+(s.re-c)))
  have hC : 0 < C := by
    have ha : 0 < b-(s.re-c) := by linarith [(abs_lt.mp hs).2]
    have hb' : 0 < b+(s.re-c) := by linarith [(abs_lt.mp hs).1]
    dsimp [C]
    positivity
  let A := ‖thetaMultiplier s‖
  let B := ‖z*thetaMultiplier w‖
  let K := 2*(A^2+B^2)*C
  have hK : 0 < 1+K := by dsimp [K];positivity
  refine ⟨‖defect s t z‖^2/(1+K),div_pos (sq_pos_of_pos (norm_pos_iff.mpr hd)) hK,?_⟩
  intro m v k
  let y (i : Fin m) := a+h*(k i:ℝ)
  let f := residual 0 v y
  let R (u : ℂ) := ∫ x : ℝ, Complex.exp (u*x)*f x
  let E := energy c b f
  have hi := (MasulloRH.finite_theta_approximation_excludes_rectangle_zeros.1
    m 0 c b 1 v y (by norm_num) (by norm_num) hl hr).1
  have Es : ‖R s‖^2 ≤ E*C := MasulloRH.exact_laplace_energy_bound_on_window f c b s hs hi
  have Ew : ‖R w‖^2 ≤ E*C := by
    have e := MasulloRH.exact_laplace_energy_bound_on_window f c b w hw hi
    rwa [hre] at e
  have E0 : 0 ≤ E := integral_nonneg (fun x => mul_nonneg (Real.exp_nonneg _) (sq_nonneg _))
  let P (u : ℂ) := ∑ i, v i * Complex.exp (u*y i)
  have shift : P w = z*P s := by
    simp only [P,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [w]
    rw [add_mul,Complex.exp_add,show Complex.exp (vertical t*(y i:ℂ)) = z from repeat_phase hh a (k i)]
    ring
  have Rs : R s = gaussian s - thetaMultiplier s * P s :=
    (MasulloRH.exact_laplace_transform_of_gaussian_theta_residual v y s h0 h1).2
  have Rw : R w = gaussian w - thetaMultiplier w * P w :=
    (MasulloRH.exact_laplace_transform_of_gaussian_theta_residual v y w (hre ▸ h0) (hre ▸ h1)).2
  have cancel : defect s t z = thetaMultiplier s*R w-(z*thetaMultiplier w)*R s := by
    rw [Rs,Rw,shift]
    change thetaMultiplier s*gaussian w-z*thetaMultiplier w*gaussian s = _
    ring
  have triangle : ‖defect s t z‖ ≤ A*‖R w‖+B*‖R s‖ := by
    rw [cancel]
    simpa only [norm_mul,A,B] using norm_sub_le (thetaMultiplier s*R w) ((z*thetaMultiplier w)*R s)
  apply (div_le_iff₀ hK).2
  calc
    ‖defect s t z‖^2 ≤ (A*‖R w‖+B*‖R s‖)^2 := pow_le_pow_left₀ (norm_nonneg _) triangle 2
    _ ≤ 2*(A^2*‖R w‖^2+B^2*‖R s‖^2) := by nlinarith only [sq_nonneg (A*‖R w‖-B*‖R s‖)]
    _ ≤ 2*(A^2*(E*C)+B^2*(E*C)) :=
      mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left Ew (sq_nonneg A))
        (mul_le_mul_of_nonneg_left Es (sq_nonneg B))) (by norm_num)
    _ ≤ E*(1+K) := by dsimp only [K];nlinarith only [E0]
