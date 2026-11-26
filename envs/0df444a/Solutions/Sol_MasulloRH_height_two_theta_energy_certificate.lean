-- Prove2me | solution 1 for MasulloRH.height_two_theta_energy_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T09:23:52.476394+00:00
-- url     : https://prove2.me/submissions/401f8242-359c-42a9-9d20-563ddc1e78ed
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MasulloRH_height_two_shared_grid_enclosures
import Theorems.Thm_MasulloRH_signed_translate_energy_upper_of_grid_enclosures
import Theorems.Thm_MasulloRH_height_two_residual_exterior_bound
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Definitions.Def_MasulloRH_GaussianThetaApproximation
import Definitions.Def_MasulloRH_HeightTwoWitness

open MeasureTheory MasulloRH MasulloRH.GaussianApproximation
set_option autoImplicit false

theorem solution :
    Integrable (fun x : ℝ => Real.exp (2*(3/4)*x + 2*(11/48)*|x|) *
      ‖residual 2 HeightTwoWitness.coeffs HeightTwoWitness.shifts x‖^2) ∧
    energy (3/4) (11/48) (residual 2 HeightTwoWitness.coeffs HeightTwoWitness.shifts) < 1/96 := by
  classical
  let h : ℝ := 1/8192
  let s : Fin 11 → ℤ := ![-3072,-2048,1024,3072,6144,8192,11264,14336,16384,18432,19456]
  have hs (i : Fin 11) : (s i : ℝ) * h = HeightTwoWitness.shifts i := by
    fin_cases i <;> norm_num [s, h, HeightTwoWitness.shifts, HeightTwoWitness.shiftsQ,
      Matrix.cons_val_zero, Matrix.cons_val_succ]
  let w (x : ℝ) := Real.exp (2*(3/4)*x + 2*(11/48)*|x|)
  let F (x : ℝ) := w x * ‖residual 2 HeightTwoWitness.coeffs HeightTwoWitness.shifts x‖^2
  have hext := MasulloRH.height_two_residual_exterior_bound
  refine ⟨hext.1, ?_⟩
  obtain ⟨P, R, W, T, U, hp, ht, htotal⟩ := MasulloRH.height_two_shared_grid_enclosures
  have hi : Integrable (fun x : ℝ => w x *
      ‖pulse 2 x - ∑ i, HeightTwoWitness.coeffs i * theta (x - (s i : ℝ)*h)‖^2) := by
    simpa only [hs, GaussianApproximation.residual] using hext.1
  have hg := MasulloRH.signed_translate_energy_upper_of_grid_enclosures 65536 (-4) h
    (by norm_num [h]) (pulse 2) theta w HeightTwoWitness.coeffs s
    (fun j => (P j : ℂ)) (fun j => (R j : ℝ)) (fun j => (W j : ℝ))
    (fun j => (T j : ℂ)) (fun j => (U j : ℝ)) hi hp ht
  have hbound := hg.trans htotal
  have right : (-4 : ℝ) + (((65536 : ℕ) : ℤ) : ℝ) * h = 4 := by norm_num [h]
  change (∫ x : ℝ in Set.Icc (-4) ((-4 : ℝ) + (((65536 : ℕ) : ℤ) : ℝ)*h),
    w x * ‖pulse 2 x - ∑ i, HeightTwoWitness.coeffs i * theta (x-(s i : ℝ)*h)‖^2) ≤ 1/100 at hbound
  rw [right] at hbound
  have hcompact : (∫ x : ℝ in Set.Icc (-4) 4, F x) ≤ 1/100 := by
    simpa only [hs, F, GaussianApproximation.residual] using hbound
  have htail : energy (3/4) (11/48) (residual 2 HeightTwoWitness.coeffs HeightTwoWitness.shifts) -
      (∫ x : ℝ in Set.Icc (-4) 4, F x) ≤ 1/10000000000 := hext.2.2
  linarith
