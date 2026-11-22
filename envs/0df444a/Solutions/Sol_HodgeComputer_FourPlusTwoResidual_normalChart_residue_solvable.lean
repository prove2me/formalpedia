-- Prove2me | solution 1 for HodgeComputer.FourPlusTwoResidual.normalChart_residue_solvable
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T08:30:38.26396+00:00
-- url     : https://prove2.me/submissions/9fc092e8-13ae-4a66-97c1-fadc30050567
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_HodgeComputer_FourPlusTwoResidual_normalChart_residue_of_coreCertificate
import Theorems.Thm_HodgeComputer_FourPlusTwoResidual_coreCertificate_iff_bipartite
import Theorems.Thm_HodgeComputer_FourPlusTwoResidual_bipartiteCoreCertificate

set_option autoImplicit false
noncomputable section

open HodgeComputer HodgeComputer.FourPlusTwoResidual

theorem solution :
    ∃ (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n),
      S ≠ 0 ∧ S.IsHomogeneous S.totalDegree ∧ IsRelPrime F S ∧
      (∀ j, (W j).IsHomogeneous (S.totalDegree + 1)) ∧
      NormalChart.residue F A S W = F * Q := by
  obtain ⟨D, N, hDN⟩ :=
    HodgeComputer.FourPlusTwoResidual.coreCertificate_iff_bipartite.mpr
      HodgeComputer.FourPlusTwoResidual.bipartiteCoreCertificate
  exact HodgeComputer.FourPlusTwoResidual.normalChart_residue_of_coreCertificate D N hDN
