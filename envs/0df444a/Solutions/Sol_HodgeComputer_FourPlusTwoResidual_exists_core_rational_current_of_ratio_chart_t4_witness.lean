-- Prove2me | solution 1 for HodgeComputer.FourPlusTwoResidual.exists_core_rational_current_of_ratio_chart_t4_witness
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-25T11:59:15.838191+00:00
-- url     : https://prove2.me/submissions/a278b7a8-8587-49bc-91b8-01a3112ffc4e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_HodgeComputer_FourPlusTwoResidual_ratio_chart_t4_yields_homogenized_source_a6t3
import Theorems.Thm_HodgeComputer_FourPlusTwoResidual_core_rational_of_homogenized_chart_source_a6t3

set_option autoImplicit false
noncomputable section

open HodgeComputer.FourPlusTwoResidual

theorem solution
    (h : ∃ (K : Type) (_ : Field K) (_ : CharZero K)
      (Dr Ds Dt : Derivation ℤ K K) (a s t P qr qs qt : K),
      a ≠ 0 ∧ t ≠ 0 ∧
        Dr a = 0 ∧ Ds a = 0 ∧ Dt a = 0 ∧
        Dr t = 0 ∧ Ds t = 0 ∧ Dt t = 1 ∧
        Ds s = 1 ∧
        (-(P * (Dr qr + Ds qs + Dt qt) -
            (2 / 3 : K) * (qr * Dr P + qs * Ds P + qt * Dt P)) = t ^ 4)) :
    ∃ (K : Type) (_ : Field K) (_ : CharZero K)
      (_ : Algebra (MvPolynomial (Fin 4) ℂ) K)
      (_ : IsFractionRing (MvPolynomial (Fin 4) ℂ) K)
      (δ : Fin 4 → Derivation ℤ K K) (v : Fin 4 → K),
      (∀ (i : Fin 4) (p : MvPolynomial (Fin 4) ℂ),
          δ i (algebraMap (MvPolynomial (Fin 4) ℂ) K p) =
            algebraMap (MvPolynomial (Fin 4) ℂ) K (MvPolynomial.pderiv i p)) ∧
        CoreRationalEquation δ v :=
  core_rational_of_homogenized_chart_source_a6t3
    (ratio_chart_t4_yields_homogenized_source_a6t3 h)
