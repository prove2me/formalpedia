-- Prove2me | solution 1 for HodgeComputer.FourPlusTwoResidual.exists_affine_dehomogenized_swept_support
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-25T12:23:24.577924+00:00
-- url     : https://prove2.me/submissions/dff483d4-faf4-48d3-bea3-0f77e6221651

import Definitions.Def_HodgeComputerFourPlusTwoSymmetry
import Definitions.Def_HodgeComputerFourPlusTwoRationalCurrent
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.Eval

set_option autoImplicit false
noncomputable section

open HodgeComputer.FourPlusTwoResidual
open MvPolynomial

/-- `affineCore` is non-constant (hence not a unit): its values at `0` and at `e₀` differ. -/
private lemma affineCore_not_isUnit : ¬ IsUnit (affineCore : MvPolynomial (Fin 3) ℂ) := by
  intro h
  rcases (isUnit_iff_eq_C_of_isReduced (R := ℂ) (σ := Fin 3)).mp h with ⟨r, _hr, heq⟩
  let z : Fin 3 → ℂ := fun _ => 0
  let e0 : Fin 3 → ℂ := fun i => if i = 0 then 1 else 0
  have hz : eval z affineCore = 1 := by
    simp [affineCore, z, eval_X, eval_C, eval_add, eval_mul, eval_pow]
  have he0 : eval e0 affineCore = (1 : ℂ) + 5 / 7 + 10 / 7 + 1 := by
    simp [affineCore, e0, eval_X, eval_C, eval_add, eval_mul, eval_pow]
  have hC0 : eval z (C r) = r := by simp [eval_C]
  have hC1 : eval e0 (C r) = r := by simp [eval_C]
  have : (1 : ℂ) = 1 + 5 / 7 + 10 / 7 + 1 := by
    calc
      (1 : ℂ) = eval z affineCore := hz.symm
      _ = eval z (C r) := by rw [heq]
      _ = r := hC0
      _ = eval e0 (C r) := hC1.symm
      _ = eval e0 affineCore := by rw [← heq]
      _ = 1 + 5 / 7 + 10 / 7 + 1 := he0
  have : (0 : ℂ) = 5 / 7 + 10 / 7 + 1 := by
    linear_combination this
  -- 5/7+10/7+1 = 15/7+1 = 22/7 ≠ 0
  have hne : (5 / 7 + 10 / 7 + 1 : ℂ) ≠ 0 := by
    norm_num
  exact hne this.symm

theorem solution
    (_hR : ∃ (R : MvPolynomial (Fin 4) ℂ),
      R ≠ 0 ∧
        ¬(core ∣ R) ∧
          ¬(core ∣ flipAB R)) :
    ∃ (B : MvPolynomial (Fin 3) ℂ),
      B ≠ 0 ∧ ¬(affineCore ∣ B) := by
  refine ⟨C (1 : ℂ), C_ne_zero.mpr one_ne_zero, ?_⟩
  intro h
  exact affineCore_not_isUnit (isUnit_of_dvd_one h)
