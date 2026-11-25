-- Prove2me | solution 1 for HodgeComputer.FourPlusTwoResidual.exists_ratio_chart_t4_witness
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-25T11:59:14.464328+00:00
-- url     : https://prove2.me/submissions/a0b1f13e-82da-4328-b967-26d94fd448dc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

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
