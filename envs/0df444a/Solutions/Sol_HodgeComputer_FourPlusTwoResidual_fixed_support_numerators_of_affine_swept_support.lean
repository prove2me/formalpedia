-- Prove2me | solution 1 for HodgeComputer.FourPlusTwoResidual.fixed_support_numerators_of_affine_swept_support
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-25T13:48:59.713675+00:00
-- url     : https://prove2.me/submissions/ef1d1b8c-d3da-4f7e-846f-d07bd4f16113
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_HodgeComputer_FourPlusTwoResidual_exists_fixed_support_equation_witness

set_option autoImplicit false
noncomputable section

open HodgeComputer.FourPlusTwoResidual

/-- The ambient hypothesis only asserts that some $H$-coprime affine support exists.
    An admissible fixed-support numerator solution may be chosen independently of that
    particular $B$; the unconditional witness supplies one. -/
theorem solution
    (_hB : ∃ (B : MvPolynomial (Fin 3) ℂ),
      B ≠ 0 ∧ ¬(affineCore ∣ B)) :
    ∃ (B : MvPolynomial (Fin 3) ℂ) (n : ℕ) (N : Fin 3 → MvPolynomial (Fin 3) ℂ),
      B ≠ 0 ∧
        ¬(affineCore ∣ B) ∧
          FixedSupportEquation B n N :=
  exists_fixed_support_equation_witness
