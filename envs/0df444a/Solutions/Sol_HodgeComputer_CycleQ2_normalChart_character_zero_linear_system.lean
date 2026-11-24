-- Prove2me | solution 1 for HodgeComputer.CycleQ2.normalChart_character_zero_linear_system
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T00:21:20.768305+00:00
-- url     : https://prove2.me/submissions/a2026150-493a-4b93-a78b-c502e66c294d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_HodgeComputerCycleQ2
import Definitions.Def_HodgeComputerNormalChart
import Definitions.Def_HodgeComputerCycleQ2SparseSource
import Definitions.Def_HodgeComputerCycleQ2ChartDivergence
import Definitions.Def_HodgeComputerCycleQ2GradedLinear
import Definitions.Def_HodgeComputerCycleQ2Character
import Definitions.Def_HodgeComputerCycleQ2NumeratorCharacter
import Theorems.Thm_HodgeComputer_CycleQ2_normalChart_character_zero_weighted_numerators

set_option autoImplicit false
open HodgeComputer HodgeComputer.CycleQ2

theorem solution :
    ∃ (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n),
      S ≠ 0 ∧ S.IsHomogeneous S.totalDegree ∧ 2 ≤ S.totalDegree ∧
      IsRelPrime F S ∧
      (∀ j, (W j).IsHomogeneous (S.totalDegree + 7)) ∧
      Q.IsHomogeneous (2 * S.totalDegree + 4) ∧
      IsCharacter 0 (S : AmbientPoly 5) ∧
      IsCharacter 1 (Q : AmbientPoly 5) ∧
      gradedLinear S W Q = gradedInhomogeneous S := by
  obtain ⟨S, W, Q, hS, hShom, hdeg, hFS, hW, hQhom, hS0, hQ1, _hWn, hchild⟩ :=
    HodgeComputer.CycleQ2.normalChart_character_zero_weighted_numerators
  exact ⟨S, W, Q, hS, hShom, hdeg, hFS, hW, hQhom, hS0, hQ1, hchild⟩
