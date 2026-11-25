-- Prove2me | solution 1 for HodgeComputer.FourPlusTwoResidual.fixedSupport_eq_of_n_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-25T16:12:24.949096+00:00
-- url     : https://prove2.me/submissions/45bd6b7c-0858-439e-8625-11dbcd58dacb

import Definitions.Def_HodgeComputerFourPlusTwoRationalCurrent

set_option autoImplicit false
noncomputable section

open MvPolynomial
open scoped BigOperators

theorem solution
    (B : MvPolynomial (Fin 3) ℂ) (N : Fin 3 → MvPolynomial (Fin 3) ℂ)
    (hB : B ≠ 0)
    (h : HodgeComputer.FourPlusTwoResidual.FixedSupportEquation B 0 N) :
    2 * (∑ i, N i * pderiv i HodgeComputer.FourPlusTwoResidual.affineCore) -
        3 * HodgeComputer.FourPlusTwoResidual.affineCore *
          (∑ i, pderiv i (N i)) =
      3 * X 1 ^ 3 := by
  have hcast : ((0 : ℕ) : MvPolynomial (Fin 3) ℂ) = 0 := by simp
  have hpow : B ^ (0 + 1) = B := by simp
  simp only [HodgeComputer.FourPlusTwoResidual.FixedSupportEquation] at h
  simp only [hcast, hpow, Nat.cast_zero, zero_mul, sub_zero, add_zero] at h
  have hz : B * (2 * (∑ i, N i * pderiv i HodgeComputer.FourPlusTwoResidual.affineCore) -
      3 * HodgeComputer.FourPlusTwoResidual.affineCore * (∑ i, pderiv i (N i))
      - 3 * X 1 ^ 3) = 0 := by
    linear_combination h
  have hz2 : 2 * (∑ i, N i * pderiv i HodgeComputer.FourPlusTwoResidual.affineCore) -
      3 * HodgeComputer.FourPlusTwoResidual.affineCore * (∑ i, pderiv i (N i))
      - 3 * X 1 ^ 3 = 0 :=
    (mul_eq_zero.mp hz).resolve_left hB
  -- The goal is exactly `hz2` read as an equation; `linarith` cannot be used here,
  -- since a polynomial ring over ℂ carries no order.
  linear_combination hz2
