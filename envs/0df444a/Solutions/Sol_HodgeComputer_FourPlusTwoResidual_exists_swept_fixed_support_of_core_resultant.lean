-- Prove2me | solution 1 for HodgeComputer.FourPlusTwoResidual.exists_swept_fixed_support_of_core_resultant
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-25T11:59:18.18272+00:00
-- url     : https://prove2.me/submissions/2348e3fa-2314-4a7a-8d28-624c9b1bdb82
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_HodgeComputer_FourPlusTwoResidual_exists_affine_dehomogenized_swept_support
import Theorems.Thm_HodgeComputer_FourPlusTwoResidual_fixed_support_numerators_of_affine_swept_support

set_option autoImplicit false
noncomputable section

open HodgeComputer.FourPlusTwoResidual

theorem solution
    (hR : ∃ (R : MvPolynomial (Fin 4) ℂ),
      R ≠ 0 ∧
        ¬(core ∣ R) ∧
          ¬(core ∣ flipAB R)) :
    ∃ (B : MvPolynomial (Fin 3) ℂ) (n : ℕ) (N : Fin 3 → MvPolynomial (Fin 3) ℂ),
      B ≠ 0 ∧
        ¬(affineCore ∣ B) ∧
          FixedSupportEquation B n N :=
  fixed_support_numerators_of_affine_swept_support
    (exists_affine_dehomogenized_swept_support hR)
