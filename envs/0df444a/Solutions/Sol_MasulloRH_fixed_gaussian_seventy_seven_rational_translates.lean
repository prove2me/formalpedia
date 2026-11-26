-- Prove2me | solution 1 for MasulloRH.fixed_gaussian_seventy_seven_rational_translates
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T20:20:57.425854+00:00
-- url     : https://prove2.me/submissions/9ccf08cd-2de5-44ad-880f-7888007e6c4c

import Theorems.Thm_MasulloRH_seven_shift_gaussian_mixture_energy
import Theorems.Thm_MasulloRH_gaussian_window_translate_mixture_energy_bound
import Theorems.Thm_MasulloRH_height_two_theta_energy_certificate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory Real MasulloRH MasulloRH.GaussianApproximation
open MasulloRH.GaussianMixture MasulloRH.FixedGaussianTest

private theorem pulse_bell (T y x : ℝ) : pulse T (x-y) = ((bell (T+1) y x : ℝ) : ℂ) := by
  unfold pulse bell
  rw [show -((T+1)^2)*(x-y)^2 = -(((T+1)*(x-y))^2) by ring]
  simp only [Complex.ofReal_mul,Complex.ofReal_exp,Complex.ofReal_neg,Complex.ofReal_pow]

private theorem diff_repr (x : ℝ) :
    difference x = pulse 0 x - ∑ i : Fin 7, (amplitude i : ℂ)*pulse 2 (x-(offset i : ℝ)) := by
  have zero := pulse_bell 0 0 x
  norm_num only [sub_zero,zero_add] at zero
  have two (i : Fin 7) : pulse 2 (x-(offset i : ℝ)) = ((bell 3 (offset i) x : ℝ) : ℂ) := by
    simpa only [show (2:ℝ)+1=3 by norm_num] using pulse_bell 2 (offset i) x
  rw [zero]
  simp_rw [two]
  unfold difference
  push_cast
  rfl

private theorem translated (x : ℝ) :
    (∑ n : Fin 77, (coefficient77 n : ℂ)*theta (x-(shift77 n : ℝ))) =
      ∑ i : Fin 7, (amplitude i : ℂ)*
        ∑ j : Fin 11, HeightTwoWitness.coeffs j*theta ((x-(offset i : ℝ))-HeightTwoWitness.shifts j) := by
  let e : (Fin 7 × Fin 11) ≃ Fin 77 := finProdFinEquiv
  let f (n : Fin 77) := (coefficient77 n : ℂ)*theta (x-(shift77 n : ℝ))
  calc
    _ = ∑ v : Fin 7 × Fin 11, f (e v) := (e.sum_comp f).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl;intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl;intro j hj
      dsimp only [f,coefficient77,shift77,e]
      simp only [Equiv.symm_apply_apply,HeightTwoWitness.coeffs,HeightTwoWitness.shifts,
        Rat.cast_mul,Rat.cast_add,sub_sub,mul_assoc]

private theorem window (c b : ℝ) (hl : 25/48 ≤ c-b) (hr : c+b ≤ 47/48) :
    energy c b (residual 0 (fun n => (coefficient77 n : ℂ)) (fun n => (shift77 n : ℝ))) < 1/16 := by
  let R := residual 2 HeightTwoWitness.coeffs HeightTwoWitness.shifts
  have decomp : residual 0 (fun n => (coefficient77 n : ℂ)) (fun n => (shift77 n : ℝ)) =
      fun x => difference x + ∑ i : Fin 7, (amplitude i : ℂ)*R (x-(offset i : ℝ)) := by
    funext x
    rw [diff_repr]
    dsimp only [R,MasulloRH.GaussianApproximation.residual]
    simp only [mul_sub,Finset.sum_sub_distrib,translated]
    ring
  obtain ⟨hD,hA,hK⟩ := MasulloRH.seven_shift_gaussian_mixture_energy c b (by linarith) (by linarith)
  obtain ⟨hR,hE⟩ := MasulloRH.height_two_theta_energy_certificate
  have posQ : ∀ i : Fin 7, 0 ≤ amplitude i := by decide +kernel
  have pos (i : Fin 7) : 0 ≤ (amplitude i : ℝ) := by exact_mod_cast posQ i
  have bound := MasulloRH.gaussian_window_translate_mixture_energy_bound
    (fun i => (amplitude i : ℝ)) (fun i => (offset i : ℝ)) pos difference R c b hl hr hD hR
  rw [decomp]
  have eqc (i : Fin 7) : (((amplitude i : ℚ) : ℝ) : ℂ) = (amplitude i : ℂ) := by norm_cast
  simp only [eqc] at bound
  apply bound.trans_lt
  have hn : 0 ≤ energy (3/4) (11/48) R := integral_nonneg (fun x => mul_nonneg (exp_nonneg _) (sq_nonneg _))
  change energy (3/4) (11/48) R < 1/96 at hE
  have prod := mul_le_mul hK.le hE.le hn (show (0:ℝ) ≤ 5/2 by norm_num)
  nlinarith only [hA,prod]

/-- An explicit array of 77 rational coefficients and shifts gives squared error
below one sixteenth throughout the indicated windows. -/
theorem solution :
    (∀ c b : ℝ, 25/48 ≤ c-b → c+b ≤ 47/48 →
      energy c b (residual 0 (fun n => (coefficient77 n : ℂ)) (fun n => (shift77 n : ℝ))) < 1/16) ∧
    (∀ k : ℕ, k ≤ 16 →
      energy (fullCenter k) (fullWidth k)
        (residual 0 (fun n => (coefficient77 n : ℂ)) (fun n => (shift77 n : ℝ))) < 1/16) := by
  refine ⟨window,?_⟩
  intro k hk
  have bound : (k:ℝ) ≤ 16 := by exact_mod_cast hk
  have hk0 : 0 < (k:ℝ)+1 := by positivity
  have lo : (1/48 : ℝ) ≤ (12287/32768)/((k:ℝ)+1) := (le_div_iff₀ hk0).2 (by linarith)
  have hi : (1/48 : ℝ) ≤ 1/((k:ℝ)+1) := (le_div_iff₀ hk0).2 (by linarith)
  have hL : 25/48 ≤ left k := by unfold left;linarith
  have hU : upper k ≤ 47/48 := max_le (by norm_num [right]) (by linarith)
  apply window <;> unfold fullCenter fullWidth <;> linarith
