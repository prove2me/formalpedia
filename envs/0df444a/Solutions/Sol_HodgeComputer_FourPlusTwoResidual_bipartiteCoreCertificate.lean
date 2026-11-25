-- Prove2me | solution 1 for HodgeComputer.FourPlusTwoResidual.bipartiteCoreCertificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-25T05:16:23.042344+00:00
-- url     : https://prove2.me/submissions/0db39ce7-59c5-452d-b77e-9b38b2d43dcc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_HodgeComputer_FourPlusTwoResidual_exists_core_rational_current
import Theorems.Thm_HodgeComputer_FourPlusTwoResidual_coreCertificate_of_rationalCurrent
import Theorems.Thm_HodgeComputer_FourPlusTwoResidual_coreCertificate_iff_bipartite

set_option autoImplicit false
noncomputable section

open HodgeComputer.FourPlusTwoResidual

theorem solution :
    ∃ (D : MvPolynomial (Fin 4) ℂ) (N : Fin 4 → MvPolynomial (Fin 4) ℂ),
      BipartiteCoreCertificate D N := by
  obtain ⟨K, fieldK, charK, algK, fracK, δ, v, h⟩ := exists_core_rational_current
  exact coreCertificate_iff_bipartite.mp
    (@coreCertificate_of_rationalCurrent K fieldK charK algK fracK δ h.1 v h.2)
