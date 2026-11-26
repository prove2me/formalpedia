-- Prove2me | solution 1 for MasulloRH.fixed_gaussian_half_tolerance_eleven_translates
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T19:43:20.54837+00:00
-- url     : https://prove2.me/submissions/5c49ec0d-9d8c-42c0-899f-c06eed8aee5c

import Definitions.Def_MasulloRH_FixedGaussianTest
import Theorems.Thm_MasulloRH_unit_gaussian_half_scale_two_difference
import Theorems.Thm_MasulloRH_height_two_theta_energy_certificate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory MasulloRH MasulloRH.GaussianApproximation Real

private theorem window (c b : ℝ) (hl : 25/48≤c-b) (hr : c+b≤7/8) :
    energy c b (residual 0 (fun i => (1/2:ℂ)*HeightTwoWitness.coeffs i) HeightTwoWitness.shifts)<1/2 := by
  let R := residual 2 HeightTwoWitness.coeffs HeightTwoWitness.shifts
  let D := fun x => pulse 0 x-(1/2:ℂ)*pulse 2 x
  let w := fun x : ℝ => exp (2*c*x+2*b*|x|)
  let W := fun x : ℝ => exp (2*(3/4)*x+2*(11/48)*|x|)
  obtain ⟨hI,hB⟩ := MasulloRH.unit_gaussian_half_scale_two_difference c b (by linarith) hr
  obtain ⟨hJ,hC⟩ := MasulloRH.height_two_theta_energy_certificate
  have wle (x : ℝ) : w x ≤ W x := by
    apply exp_le_exp.2
    rcases le_total 0 x with hx|hx
    · rw [abs_of_nonneg hx];nlinarith [mul_nonneg (sub_nonneg.mpr hr) hx]
    · rw [abs_of_nonpos hx];nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hl) hx]
  have decomp (x : ℝ) : residual 0 (fun i => (1/2:ℂ)*HeightTwoWitness.coeffs i) HeightTwoWitness.shifts x = D x + (1/2:ℂ)*R x := by
    dsimp only [D,R,MasulloRH.GaussianApproximation.residual]
    rw [mul_sub,Finset.mul_sum]
    simp only [mul_assoc]
    ring
  have H (x : ℝ) : ‖D x+(1/2:ℂ)*R x‖^2 ≤ (11/10)*‖D x‖^2+(11/4)*‖R x‖^2 := by
    have t := norm_add_le (D x) ((1/2:ℂ)*R x)
    rw [norm_mul] at t
    norm_num at t
    have ts := sq_le_sq' (by linarith [norm_nonneg (D x),norm_nonneg (R x),norm_nonneg (D x+(1/2:ℂ)*R x)]) t
    nlinarith only [ts,sq_nonneg (‖D x‖-5*‖R x‖)]
  have iD : Integrable (fun x => (11/10)*(w x*‖D x‖^2)) := hI.const_mul _
  have iR : Integrable (fun x => (11/4)*(W x*‖R x‖^2)) := hJ.const_mul _
  have cap : energy c b (residual 0 (fun i => (1/2:ℂ)*HeightTwoWitness.coeffs i) HeightTwoWitness.shifts) ≤
      ∫ x : ℝ, (11/10)*(w x*‖D x‖^2)+(11/4)*(W x*‖R x‖^2) := by
    apply integral_mono_of_nonneg (ae_of_all _ (fun _ => mul_nonneg (exp_nonneg _) (sq_nonneg _))) (iD.add iR)
    apply ae_of_all;intro x
    change w x * ‖residual 0 (fun i => (1/2:ℂ)*HeightTwoWitness.coeffs i) HeightTwoWitness.shifts x‖^2 ≤ (11/10)*(w x*‖D x‖^2)+(11/4)*(W x*‖R x‖^2)
    rw [decomp]
    have one := mul_le_mul_of_nonneg_left (H x) (exp_nonneg _ : 0≤w x)
    have two := mul_le_mul_of_nonneg_right (wle x) (sq_nonneg ‖R x‖)
    nlinarith only [one,two]
  rw [integral_add iD iR,integral_const_mul,integral_const_mul] at cap
  change (∫ x : ℝ, w x*‖D x‖^2) < 17/40 at hB
  change (∫ x : ℝ, W x*‖R x‖^2) < 1/96 at hC
  linarith

open MasulloRH.FixedGaussianTest

/-- Halving the eleven scale-two coefficients gives a fixed rational witness on each specified window and discharges the first positive tolerance at index two. -/
theorem solution :
    (∀ c b : ℝ, 25/48≤c-b → c+b≤7/8 →
      energy c b (residual 0 (fun i => (1/2:ℂ)*HeightTwoWitness.coeffs i) HeightTwoWitness.shifts)<1/2) ∧
    (∃ (m : ℕ) (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ),
      energy (fullCenter 2) (fullWidth 2) (residual 0
        (fun i => ((a i).1:ℂ)+((a i).2:ℂ)*Complex.I) (fun i => (y i:ℝ))) < 1/2) := by
  refine ⟨window,11,fun i => (HeightTwoWitness.coeffsQ i/2,0),HeightTwoWitness.shiftsQ,?_⟩
  have h := window (fullCenter 2) (fullWidth 2)
    (by norm_num [fullCenter,fullWidth,left,right,upper]) (by norm_num [fullCenter,fullWidth,left,right,upper])
  have he : (fun i : Fin 11 => ((HeightTwoWitness.coeffsQ i/2:ℚ):ℂ)+(0:ℂ)*Complex.I) =
      fun i => (1/2:ℂ)*HeightTwoWitness.coeffs i := by
    funext i;unfold HeightTwoWitness.coeffs;push_cast;ring
  change energy (fullCenter 2) (fullWidth 2) (residual 0
    (fun i => ((HeightTwoWitness.coeffsQ i/2:ℚ):ℂ)+((0:ℚ):ℂ)*Complex.I) HeightTwoWitness.shifts) < 1/2
  simp only [Rat.cast_zero,he]
  exact h
