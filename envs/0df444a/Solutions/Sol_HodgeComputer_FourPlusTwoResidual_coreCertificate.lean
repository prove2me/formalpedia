-- Prove2me | solution 1 for HodgeComputer.FourPlusTwoResidual.coreCertificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T08:30:37.59194+00:00
-- url     : https://prove2.me/submissions/431e705a-6274-44f8-b08c-ea82e8e1117f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_HodgeComputer_FourPlusTwoResidual_coreCertificate_iff_bipartite
import Theorems.Thm_HodgeComputer_FourPlusTwoResidual_bipartiteCoreCertificate

set_option autoImplicit false
noncomputable section

theorem solution :
    ∃ (D : MvPolynomial (Fin 4) ℂ) (N : Fin 4 → MvPolynomial (Fin 4) ℂ),
      HodgeComputer.FourPlusTwoResidual.CoreCertificate D N :=
  HodgeComputer.FourPlusTwoResidual.coreCertificate_iff_bipartite.mpr
    HodgeComputer.FourPlusTwoResidual.bipartiteCoreCertificate
