-- Prove2me | solution 1 for HodgeComputer.CycleQ2.normalChart_chart_divergence_membership
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T23:47:56.662815+00:00
-- url     : https://prove2.me/submissions/5a28d860-d55c-44d1-87a4-79dcecbd6e52
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_HodgeComputerCycleQ2
import Definitions.Def_HodgeComputerNormalChart
import Definitions.Def_HodgeComputerCycleQ2SparseSource
import Definitions.Def_HodgeComputerCycleQ2ChartDivergence
import Theorems.Thm_HodgeComputer_CycleQ2_normalChart_homogeneous_quotient_membership

set_option autoImplicit false
open HodgeComputer HodgeComputer.CycleQ2

theorem solution :
    ∃ (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n),
      S ≠ 0 ∧ S.IsHomogeneous S.totalDegree ∧ 2 ≤ S.totalDegree ∧
      IsRelPrime F S ∧
      (∀ j, (W j).IsHomogeneous (S.totalDegree + 7)) ∧
      divergenceCarrier S W = F ^ 2 * Q := by
  obtain ⟨S, W, Q, hS, hShom, hdeg, hFS, hW, _hQhom, hchild⟩ :=
    HodgeComputer.CycleQ2.normalChart_homogeneous_quotient_membership
  exact ⟨S, W, Q, hS, hShom, hdeg, hFS, hW, hchild⟩
