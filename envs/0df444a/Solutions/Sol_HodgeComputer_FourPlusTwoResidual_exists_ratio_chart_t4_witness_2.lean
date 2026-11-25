-- Prove2me | solution 2 for HodgeComputer.FourPlusTwoResidual.exists_ratio_chart_t4_witness
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-25T12:54:12.642351+00:00
-- url     : https://prove2.me/submissions/c7ec86b6-18a7-4e90-b055-1de530f52df8

import Theorems.Thm_HodgeComputer_FourPlusTwoResidual_exists_hermite_pade_flat_moment_section_e3
import Theorems.Thm_HodgeComputer_FourPlusTwoResidual_ratio_chart_t4_of_flat_moment_section_e3

set_option autoImplicit false
noncomputable section

open HodgeComputer.FourPlusTwoResidual

theorem solution :
    ∃ (K : Type) (_ : Field K) (_ : CharZero K)
      (Dr Ds Dt : Derivation ℤ K K) (a s t P qr qs qt : K),
      a ≠ 0 ∧ t ≠ 0 ∧
        Dr a = 0 ∧ Ds a = 0 ∧ Dt a = 0 ∧
        Dr t = 0 ∧ Ds t = 0 ∧ Dt t = 1 ∧
        Ds s = 1 ∧
        (-(P * (Dr qr + Ds qs + Dt qt) -
            (2 / 3 : K) * (qr * Dr P + qs * Ds P + qt * Dt P)) = t ^ 4) :=
  ratio_chart_t4_of_flat_moment_section_e3 exists_hermite_pade_flat_moment_section_e3
