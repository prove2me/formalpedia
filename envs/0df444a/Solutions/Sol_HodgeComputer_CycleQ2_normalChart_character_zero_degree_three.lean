-- Prove2me | solution 1 for HodgeComputer.CycleQ2.normalChart_character_zero_degree_three
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T14:17:41.784842+00:00
-- url     : https://prove2.me/submissions/a995b6f2-9495-4428-8ccd-5ff94ad10f08
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_HodgeComputerCycleQ2
import Definitions.Def_HodgeComputerNormalChart
import Definitions.Def_HodgeComputerCycleQ2SparseSource
import Definitions.Def_HodgeComputerCycleQ2ChartDivergence
import Definitions.Def_HodgeComputerCycleQ2GradedLinear
import Definitions.Def_HodgeComputerCycleQ2Character
import Definitions.Def_HodgeComputerCycleQ2NumeratorCharacter
import Theorems.Thm_HodgeComputer_CycleQ2_normalChart_character_zero_degree_three_X2_cubed

set_option autoImplicit false
open HodgeComputer HodgeComputer.CycleQ2

theorem solution :
    ∃ (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n),
      S ≠ 0 ∧ S.IsHomogeneous 3 ∧ S.totalDegree = 3 ∧
      IsRelPrime F S ∧
      (∀ j, (W j).IsHomogeneous (3 + 7)) ∧
      Q.IsHomogeneous (2 * 3 + 4) ∧
      IsCharacter 0 (S : AmbientPoly 5) ∧
      IsCharacter 1 (Q : AmbientPoly 5) ∧
      (∀ j, IsCharacter (numeratorCharacter j) (W j : AmbientPoly 5)) ∧
      gradedLinear S W Q = gradedInhomogeneous S := by
  obtain ⟨S, W, Q, _hEq, hS, hShom, hdegEq, hFS, hW, hQhom, hS0, hQ1, hWn, hchild⟩ :=
    HodgeComputer.CycleQ2.normalChart_character_zero_degree_three_X2_cubed
  exact ⟨S, W, Q, hS, hShom, hdegEq, hFS, hW, hQhom, hS0, hQ1, hWn, hchild⟩
