-- Prove2me | solution 1 for HodgeComputer.FourPlusTwoResidual.exists_contact_gm_hermite_pade_section_e3
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-25T14:17:08.487603+00:00
-- url     : https://prove2.me/submissions/e00ce989-efed-4b18-bc4b-215659be41af

import Theorems.Thm_HodgeComputer_FourPlusTwoResidual_exists_hermite_pade_flat_moment_section_e3

set_option autoImplicit false
noncomputable section

open HodgeComputer.FourPlusTwoResidual

/-!
Honest REDUCED strengthening placeholder: the formal Lean type is identical to the
proved algebraic hermite leaf and does not carry geometric provenance. We discharge
the formal obligation by reduction to `exists_hermite_pade_flat_moment_section_e3`,
recording in the explanation that the contact/GM certificate remains open at the
natural-language level.
-/

theorem solution :
    ∃ (K : Type) (_ : Field K) (_ : CharZero K)
      (Dr Ds Dt : Derivation ℤ K K) (a s t P : K)
      (n : ℕ) (c : Fin n → K) (T0 T2 T4 : Fin n → K)
      (qr qs qt : K),
      n ≠ 0 ∧
        a ≠ 0 ∧ t ≠ 0 ∧
        Dr a = 0 ∧ Ds a = 0 ∧ Dt a = 0 ∧
        Dr t = 0 ∧ Ds t = 0 ∧ Dt t = 1 ∧
        Ds s = 1 ∧
        (∑ j : Fin n, c j * T0 j = 0) ∧
        (∑ j : Fin n, c j * T2 j = 0) ∧
        (∑ j : Fin n, c j * T4 j = 1) ∧
        (-(P * (Dr qr + Ds qs + Dt qt) -
            (2 / 3 : K) * (qr * Dr P + qs * Ds P + qt * Dt P)) =
          (∑ j : Fin n, c j * T0 j) +
            (∑ j : Fin n, c j * T2 j) * t ^ 2 +
              (∑ j : Fin n, c j * T4 j) * t ^ 4) :=
  exists_hermite_pade_flat_moment_section_e3
