-- Prove2me | solution 1 for HodgeComputer.PolarizedK3Remainder.F_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T22:52:03.678333+00:00
-- url     : https://prove2.me/submissions/5a386ddc-58e5-4323-9d4a-576268fd7caf

import Definitions.Def_HodgeComputerPolarizedK3Remainder
import Mathlib.Tactic.NormNum
import Mathlib.RingTheory.Polynomial.Basic

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section

open HodgeComputer HodgeComputer.PolarizedK3Remainder MvPolynomial

/-- View `F` as a univariate polynomial in `X₀` with coefficients in the remaining five variables. -/
private abbrev split := MvPolynomial.finSuccEquiv ℂ 5

private lemma split_C (c : ℂ) : split (MvPolynomial.C c) = Polynomial.C (MvPolynomial.C c) := by
  simp [split, finSuccEquiv_apply]

private lemma split_X0 : split (MvPolynomial.X (0 : Fin 6)) = Polynomial.X := by
  exact finSuccEquiv_X_zero

private lemma split_X1 : split (MvPolynomial.X (1 : Fin 6)) = Polynomial.C (MvPolynomial.X (0 : Fin 5)) := by
  exact finSuccEquiv_X_succ (j := (0 : Fin 5))

private lemma split_X2 : split (MvPolynomial.X (2 : Fin 6)) = Polynomial.C (MvPolynomial.X (1 : Fin 5)) := by
  exact finSuccEquiv_X_succ (j := (1 : Fin 5))

private lemma split_X3 : split (MvPolynomial.X (3 : Fin 6)) = Polynomial.C (MvPolynomial.X (2 : Fin 5)) := by
  exact finSuccEquiv_X_succ (j := (2 : Fin 5))

private lemma split_X4 : split (MvPolynomial.X (4 : Fin 6)) = Polynomial.C (MvPolynomial.X (3 : Fin 5)) := by
  exact finSuccEquiv_X_succ (j := (3 : Fin 5))

private lemma split_X5 : split (MvPolynomial.X (5 : Fin 6)) = Polynomial.C (MvPolynomial.X (4 : Fin 5)) := by
  exact finSuccEquiv_X_succ (j := (4 : Fin 5))

/-- Leading coefficient of `F` as a degree-6 polynomial in `X₀` is the constant `1`. -/
private lemma top_coeff : (split F).coeff 6 = MvPolynomial.C (1 / 1 : ℂ) := by
  simp only [F, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, split_C,
    split_X0, split_X1, split_X2, split_X3, split_X4, split_X5]
  simp only [← Polynomial.C_pow, Polynomial.coeff_add, Polynomial.coeff_sub,
    Polynomial.coeff_neg, Polynomial.coeff_mul_C, Polynomial.coeff_ofNat_mul,
    Polynomial.coeff_X_pow, Polynomial.coeff_C, Polynomial.coeff_X]
  norm_num
  all_goals simp [div_eq_mul_inv]
  all_goals norm_num only [map_natCast, map_intCast]
  all_goals exact (map_natCast (MvPolynomial.C : ℂ →+* MvPolynomial (Fin 5) ℂ) 1).symm

theorem solution : F ≠ 0 := by
  intro hF
  have htop := top_coeff
  rw [hF, map_zero, Polynomial.coeff_zero] at htop
  have : (1 : MvPolynomial (Fin 5) ℂ) = 0 := by
    simpa [map_one] using htop.symm
  exact one_ne_zero this
