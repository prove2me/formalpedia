-- Prove2me | solution 2 for HodgeComputer.FourPlusTwoResidual.bipartiteCoreCertificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-25T05:17:58.887797+00:00
-- url     : https://prove2.me/submissions/27c92881-e31a-4ab3-8236-16f9668078a8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_HodgeComputer_FourPlusTwoResidual_exists_fixed_support_core_solution
import Theorems.Thm_HodgeComputer_FourPlusTwoResidual_coreCertificate_of_fixedSupport
import Theorems.Thm_HodgeComputer_FourPlusTwoResidual_coreCertificate_iff_bipartite

set_option autoImplicit false
noncomputable section

open HodgeComputer.FourPlusTwoResidual

theorem solution :
    ∃ (D : MvPolynomial (Fin 4) ℂ) (N : Fin 4 → MvPolynomial (Fin 4) ℂ),
      BipartiteCoreCertificate D N := by
  obtain ⟨B, n, N, hB, hEq⟩ := exists_fixed_support_core_solution
  exact coreCertificate_iff_bipartite.mp (coreCertificate_of_fixedSupport B n N hB hEq)
