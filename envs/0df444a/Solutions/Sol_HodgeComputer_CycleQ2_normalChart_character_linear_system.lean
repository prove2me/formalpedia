-- Prove2me | solution 1 for HodgeComputer.CycleQ2.normalChart_character_linear_system
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T00:07:54.311923+00:00
-- url     : https://prove2.me/submissions/28042f5c-59d3-4857-ac6b-654da1b12ca5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_HodgeComputerCycleQ2
import Definitions.Def_HodgeComputerNormalChart
import Definitions.Def_HodgeComputerCycleQ2SparseSource
import Definitions.Def_HodgeComputerCycleQ2ChartDivergence
import Definitions.Def_HodgeComputerCycleQ2GradedLinear
import Definitions.Def_HodgeComputerCycleQ2Character
import Theorems.Thm_HodgeComputer_CycleQ2_normalChart_character_zero_linear_system

set_option autoImplicit false
open HodgeComputer HodgeComputer.CycleQ2

theorem solution :
    ∃ (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n) (χ : ZMod 6),
      S ≠ 0 ∧ S.IsHomogeneous S.totalDegree ∧ 2 ≤ S.totalDegree ∧
      IsRelPrime F S ∧
      (∀ j, (W j).IsHomogeneous (S.totalDegree + 7)) ∧
      Q.IsHomogeneous (2 * S.totalDegree + 4) ∧
      IsCharacter χ (S : AmbientPoly 5) ∧
      IsCharacter (2 * χ + 1) (Q : AmbientPoly 5) ∧
      gradedLinear S W Q = gradedInhomogeneous S := by
  obtain ⟨S, W, Q, hS, hShom, hdeg, hFS, hW, hQhom, hS0, hQ1, hchild⟩ :=
    HodgeComputer.CycleQ2.normalChart_character_zero_linear_system
  refine ⟨S, W, Q, 0, hS, hShom, hdeg, hFS, hW, hQhom, hS0, ?_, hchild⟩
  simpa using hQ1
