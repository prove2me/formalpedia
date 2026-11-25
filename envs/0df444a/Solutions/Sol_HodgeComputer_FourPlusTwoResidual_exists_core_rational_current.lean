-- Prove2me | solution 1 for HodgeComputer.FourPlusTwoResidual.exists_core_rational_current
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-25T05:50:29.811365+00:00
-- url     : https://prove2.me/submissions/6f5f8316-8610-4fc6-9233-9ebf18c66dca
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_HodgeComputer_FourPlusTwoResidual_exists_ratio_chart_t4_witness
import Theorems.Thm_HodgeComputer_FourPlusTwoResidual_exists_core_rational_current_of_ratio_chart_t4_witness

set_option autoImplicit false
noncomputable section

open HodgeComputer.FourPlusTwoResidual

theorem solution :
    ∃ (K : Type) (_ : Field K) (_ : CharZero K)
      (_ : Algebra (MvPolynomial (Fin 4) ℂ) K)
      (_ : IsFractionRing (MvPolynomial (Fin 4) ℂ) K)
      (δ : Fin 4 → Derivation ℤ K K) (v : Fin 4 → K),
      (∀ (i : Fin 4) (p : MvPolynomial (Fin 4) ℂ),
          δ i (algebraMap (MvPolynomial (Fin 4) ℂ) K p) =
            algebraMap (MvPolynomial (Fin 4) ℂ) K (MvPolynomial.pderiv i p)) ∧
        CoreRationalEquation δ v :=
  exists_core_rational_current_of_ratio_chart_t4_witness exists_ratio_chart_t4_witness
