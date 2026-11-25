-- Prove2me | solution 1 for HodgeComputer.FourPlusTwoResidual.exists_geometric_projected_swept_resultant
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-25T13:56:44.1467+00:00
-- url     : https://prove2.me/submissions/db467969-55e8-47ef-ab8b-c5d273753cab

import Definitions.Def_HodgeComputerFourPlusTwoSymmetry
import Theorems.Thm_HodgeComputer_FourPlusTwoResidual_core_irreducible
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.MvPolynomial.Homogeneous

set_option autoImplicit false
noncomputable section

open HodgeComputer.FourPlusTwoResidual
open MvPolynomial

private lemma core_isHomogeneous_six :
    (core : MvPolynomial (Fin 4) ℂ).IsHomogeneous 6 := by
  simp only [core]
  repeat' apply IsHomogeneous.add
  · exact isHomogeneous_X_pow (R := ℂ) (0 : Fin 4) 6
  · exact ((isHomogeneous_C (σ := Fin 4) (5 / 7 : ℂ)).mul
      (isHomogeneous_X_pow (R := ℂ) (0 : Fin 4) 5)).mul (isHomogeneous_X (R := ℂ) 1)
  · exact ((((isHomogeneous_C (σ := Fin 4) (5 / 7 : ℂ)).mul
      (isHomogeneous_X_pow (R := ℂ) (0 : Fin 4) 3)).mul (isHomogeneous_X (R := ℂ) 1)).mul
      (isHomogeneous_X (R := ℂ) 2)).mul (isHomogeneous_X (R := ℂ) 3)
  · exact ((isHomogeneous_C (σ := Fin 4) (10 / 7 : ℂ)).mul
      (isHomogeneous_X (R := ℂ) (0 : Fin 4))).mul (isHomogeneous_X_pow (R := ℂ) 1 5)
  · exact ((((isHomogeneous_C (σ := Fin 4) (10 / 7 : ℂ)).mul
      (isHomogeneous_X (R := ℂ) (0 : Fin 4))).mul (isHomogeneous_X (R := ℂ) 1)).mul
      (isHomogeneous_X_pow (R := ℂ) 2 3)).mul (isHomogeneous_X (R := ℂ) 3)
  · exact isHomogeneous_X_pow (R := ℂ) (1 : Fin 4) 6
  · exact isHomogeneous_X_pow (R := ℂ) (2 : Fin 4) 6
  · exact ((isHomogeneous_C (σ := Fin 4) (5 / 7 : ℂ)).mul
      (isHomogeneous_X_pow (R := ℂ) (2 : Fin 4) 5)).mul (isHomogeneous_X (R := ℂ) 3)
  · exact ((isHomogeneous_C (σ := Fin 4) (15 / 7 : ℂ)).mul
      (isHomogeneous_X (R := ℂ) (2 : Fin 4))).mul (isHomogeneous_X_pow (R := ℂ) 3 5)
  · exact isHomogeneous_X_pow (R := ℂ) (3 : Fin 4) 6

private lemma core_ne_zero' : (core : MvPolynomial (Fin 4) ℂ) ≠ 0 :=
  Irreducible.ne_zero core_irreducible

private lemma core_totalDegree_eq_six :
    totalDegree (core : MvPolynomial (Fin 4) ℂ) = 6 :=
  IsHomogeneous.totalDegree core_isHomogeneous_six core_ne_zero'

private lemma not_core_dvd_X0 : ¬(core ∣ (X 0 : MvPolynomial (Fin 4) ℂ)) := by
  intro h
  have hle := totalDegree_le_of_dvd_of_isDomain (R := ℂ) h (X_ne_zero (0 : Fin 4))
  have hx : totalDegree (X (0 : Fin 4) : MvPolynomial (Fin 4) ℂ) = 1 := totalDegree_X _
  have : 6 ≤ (1 : ℕ) := by
    calc
      6 = totalDegree (core : MvPolynomial (Fin 4) ℂ) := core_totalDegree_eq_six.symm
      _ ≤ totalDegree (X (0 : Fin 4) : MvPolynomial (Fin 4) ℂ) := hle
      _ = 1 := hx
  omega

private lemma X0_not_isUnit : ¬ IsUnit (X 0 : MvPolynomial (Fin 4) ℂ) := by
  intro h
  rcases (isUnit_iff_eq_C_of_isReduced (R := ℂ) (σ := Fin 4)).mp h with ⟨r, _hr, heq⟩
  have : (0 : ℂ) = 1 := by
    calc
      (0 : ℂ) = eval (fun _ : Fin 4 => (0 : ℂ)) (X 0) := by simp
      _ = eval (fun _ : Fin 4 => (0 : ℂ)) (C r) := by rw [heq]
      _ = r := by simp
      _ = eval (fun i : Fin 4 => if i = 0 then (1 : ℂ) else 0) (C r) := by simp
      _ = eval (fun i : Fin 4 => if i = 0 then (1 : ℂ) else 0) (X 0) := by rw [← heq]
      _ = 1 := by simp
  exact zero_ne_one this

theorem solution :
    ∃ (R : MvPolynomial (Fin 4) ℂ),
      R ≠ 0 ∧
        ¬ IsUnit R ∧
          ¬(core ∣ R) ∧
            ¬(core ∣ flipAB R) := by
  refine ⟨X 0, X_ne_zero _, X0_not_isUnit, not_core_dvd_X0, ?_⟩
  · have hflip : flipAB (X 0) = -(X 0) := by
      simp [flipAB, aeval_X]
    rw [hflip]
    intro h
    exact not_core_dvd_X0 (by simpa [dvd_neg] using h)
