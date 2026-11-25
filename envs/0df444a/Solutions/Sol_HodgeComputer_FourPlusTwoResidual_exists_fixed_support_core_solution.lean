-- Prove2me | solution 1 for HodgeComputer.FourPlusTwoResidual.exists_fixed_support_core_solution
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-25T05:50:31.634282+00:00
-- url     : https://prove2.me/submissions/8eb3cf72-d1ec-4ad1-bbb8-67488a44d15c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_HodgeComputer_FourPlusTwoResidual_exists_projected_swept_sign_translate_denominator
import Theorems.Thm_HodgeComputer_FourPlusTwoResidual_exists_swept_fixed_support_of_core_resultant

set_option autoImplicit false
noncomputable section

open HodgeComputer.FourPlusTwoResidual

theorem solution :
    ∃ (B : MvPolynomial (Fin 3) ℂ) (n : ℕ) (N : Fin 3 → MvPolynomial (Fin 3) ℂ),
      B ≠ 0 ∧ FixedSupportEquation B n N := by
  obtain ⟨B, n, N, hB, _hcop, hEq⟩ :=
    exists_swept_fixed_support_of_core_resultant exists_projected_swept_sign_translate_denominator
  exact ⟨B, n, N, hB, hEq⟩
