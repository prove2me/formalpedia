-- Prove2me | solution 1 for HodgeComputer.FourPlusTwoResidual.fixedSupport_of_denominator_free_system
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-25T16:28:10.24716+00:00
-- url     : https://prove2.me/submissions/ac5edf72-f96d-4134-b5f5-710d55f396c1

import Definitions.Def_HodgeComputerFourPlusTwoRationalCurrent

set_option autoImplicit false
noncomputable section

open MvPolynomial
open scoped BigOperators

/-- **The denominator-free system produces a fixed-support solution.** The exponent-zero
branch of the affine fixed-support equation is *equivalent* to the denominator-free
polynomial system $2 (N \cdot \nabla h) - 3 h\, \mathrm{div}\,N = 3 y^3$: if that system
holds, then the fixed-support equation holds at $n = 0$ for *every* denominator $B$, so
in particular for any admissible one. Together with
`fixedSupport_eq_of_n_eq_zero` this makes the exponent-zero branch an equivalence
between two statements that do not mention the denominator at all. -/
theorem solution :
    ∀ (B : MvPolynomial (Fin 3) ℂ) (N : Fin 3 → MvPolynomial (Fin 3) ℂ),
      2 * (∑ i, N i * pderiv i HodgeComputer.FourPlusTwoResidual.affineCore) -
          3 * HodgeComputer.FourPlusTwoResidual.affineCore * (∑ i, pderiv i (N i)) =
        3 * X 1 ^ 3 →
        HodgeComputer.FourPlusTwoResidual.FixedSupportEquation B 0 N := by
  intro B N h
  simp only [HodgeComputer.FourPlusTwoResidual.FixedSupportEquation, Nat.cast_zero,
    zero_mul, sub_zero, Nat.zero_add, pow_one]
  calc 2 * B * (∑ i, N i * pderiv i HodgeComputer.FourPlusTwoResidual.affineCore) -
        3 * HodgeComputer.FourPlusTwoResidual.affineCore * (B * (∑ i, pderiv i (N i)))
      = B * (2 * (∑ i, N i * pderiv i HodgeComputer.FourPlusTwoResidual.affineCore)
          - 3 * HodgeComputer.FourPlusTwoResidual.affineCore * (∑ i, pderiv i (N i))) := by ring
    _ = B * (3 * X 1 ^ 3) := by rw [h]
    _ = 3 * X 1 ^ 3 * B := by ring
