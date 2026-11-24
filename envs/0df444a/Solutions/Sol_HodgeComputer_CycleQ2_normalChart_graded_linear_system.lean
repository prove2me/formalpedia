-- Prove2me | solution 1 for HodgeComputer.CycleQ2.normalChart_graded_linear_system
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T00:03:02.961553+00:00
-- url     : https://prove2.me/submissions/5ed47f16-1ef8-45ae-b406-154d8a4c986a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_HodgeComputerCycleQ2
import Definitions.Def_HodgeComputerNormalChart
import Definitions.Def_HodgeComputerCycleQ2SparseSource
import Definitions.Def_HodgeComputerCycleQ2ChartDivergence
import Definitions.Def_HodgeComputerCycleQ2GradedLinear
import Definitions.Def_HodgeComputerCycleQ2Character
import Theorems.Thm_HodgeComputer_CycleQ2_normalChart_character_linear_system

set_option autoImplicit false
open HodgeComputer HodgeComputer.CycleQ2

theorem solution :
    ∃ (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n),
      S ≠ 0 ∧ S.IsHomogeneous S.totalDegree ∧ 2 ≤ S.totalDegree ∧
      IsRelPrime F S ∧
      (∀ j, (W j).IsHomogeneous (S.totalDegree + 7)) ∧
      Q.IsHomogeneous (2 * S.totalDegree + 4) ∧
      gradedLinear S W Q = gradedInhomogeneous S := by
  obtain ⟨S, W, Q, χ, hS, hShom, hdeg, hFS, hW, hQhom, _hSch, _hQch, hchild⟩ :=
    HodgeComputer.CycleQ2.normalChart_character_linear_system
  exact ⟨S, W, Q, hS, hShom, hdeg, hFS, hW, hQhom, hchild⟩
