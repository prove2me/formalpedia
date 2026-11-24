-- Prove2me | solution 1 for HodgeComputer.CycleQ2.normalChart_character_zero_weighted_numerators
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T00:30:02.951657+00:00
-- url     : https://prove2.me/submissions/e4c8ee95-e8be-49bf-9faf-db9a116febd3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_HodgeComputerCycleQ2
import Definitions.Def_HodgeComputerNormalChart
import Definitions.Def_HodgeComputerCycleQ2SparseSource
import Definitions.Def_HodgeComputerCycleQ2ChartDivergence
import Definitions.Def_HodgeComputerCycleQ2GradedLinear
import Definitions.Def_HodgeComputerCycleQ2Character
import Definitions.Def_HodgeComputerCycleQ2NumeratorCharacter
import Theorems.Thm_HodgeComputer_CycleQ2_normalChart_character_zero_weighted_numerators_at_degree

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
      (∀ j, IsCharacter (numeratorCharacter j) (W j : AmbientPoly 5)) ∧
      gradedLinear S W Q = gradedInhomogeneous S := by
  obtain ⟨e, S, W, Q, he, hS, hShom, hdegEq, hFS, hW, hQhom, hS0, hQ1, hWn, hchild⟩ :=
    HodgeComputer.CycleQ2.normalChart_character_zero_weighted_numerators_at_degree
  refine ⟨S, W, Q, hS, ?_, ?_, hFS, ?_, ?_, hS0, hQ1, hWn, hchild⟩
  · rw [hdegEq]
    exact hShom
  · rw [hdegEq]
    exact he
  · intro j
    rw [hdegEq]
    exact hW j
  · rw [hdegEq]
    exact hQhom
