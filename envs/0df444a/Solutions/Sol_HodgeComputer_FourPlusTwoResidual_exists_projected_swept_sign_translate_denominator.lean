-- Prove2me | solution 1 for HodgeComputer.FourPlusTwoResidual.exists_projected_swept_sign_translate_denominator
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-25T11:51:59.18988+00:00
-- url     : https://prove2.me/submissions/9c87f4f1-a571-4f72-8ccd-25c403e03059

import Definitions.Def_HodgeComputerFourPlusTwoSymmetry
import Theorems.Thm_HodgeComputer_FourPlusTwoResidual_core_irreducible

set_option autoImplicit false
noncomputable section

open HodgeComputer.FourPlusTwoResidual
open MvPolynomial

theorem solution :
    ∃ (R : MvPolynomial (Fin 4) ℂ),
      R ≠ 0 ∧
        ¬(core ∣ R) ∧
          ¬(core ∣ flipAB R) := by
  refine ⟨C (1 : ℂ), ?ne, ?n1, ?n2⟩
  · exact C_ne_zero.mpr one_ne_zero
  · intro h
    exact (Irreducible.not_isUnit core_irreducible) (isUnit_of_dvd_one h)
  · have h1 : flipAB (C (1 : ℂ)) = C 1 := by
      simpa using (AlgHom.map_one flipAB)
    rw [h1]
    intro h
    exact (Irreducible.not_isUnit core_irreducible) (isUnit_of_dvd_one h)
