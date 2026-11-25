-- Prove2me | solution 1 for HodgeComputer.FourPlusTwoResidual.exists_fixed_support_equation_witness
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-25T14:29:03.677863+00:00
-- url     : https://prove2.me/submissions/44d5f2a5-d311-48c0-86f7-897817adf751
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_HodgeComputer_FourPlusTwoResidual_exists_admissible_affine_denominator
import Theorems.Thm_HodgeComputer_FourPlusTwoResidual_fixed_support_linear_system_solvable

set_option autoImplicit false
noncomputable section

open HodgeComputer.FourPlusTwoResidual

/-- Parent witness splits into (i) nonempty admissible-denominator locus and
(ii) Macaulay solvability of `FixedSupportEquation` on some admissible support.
The second leaf already returns a full admissible numerator triple; the first
records that the locus is nonempty (e.g. `B = 1`). -/
theorem solution :
    ∃ (B : MvPolynomial (Fin 3) ℂ) (n : ℕ) (N : Fin 3 → MvPolynomial (Fin 3) ℂ),
      B ≠ 0 ∧
        ¬(affineCore ∣ B) ∧
          FixedSupportEquation B n N := by
  obtain ⟨_B0, _hB0, _hadm⟩ := exists_admissible_affine_denominator
  exact fixed_support_linear_system_solvable
