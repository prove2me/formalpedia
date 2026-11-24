-- Prove2me | solution 1 for HodgeComputer.CycleQ2.normalChart_character_zero_degree_case_split
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T01:26:09.908387+00:00
-- url     : https://prove2.me/submissions/b42a4caa-75ac-4a56-ae6d-c2b66ddcf7f5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_HodgeComputerCycleQ2
import Definitions.Def_HodgeComputerNormalChart
import Definitions.Def_HodgeComputerCycleQ2SparseSource
import Definitions.Def_HodgeComputerCycleQ2ChartDivergence
import Definitions.Def_HodgeComputerCycleQ2GradedLinear
import Definitions.Def_HodgeComputerCycleQ2Character
import Definitions.Def_HodgeComputerCycleQ2NumeratorCharacter
import Theorems.Thm_HodgeComputer_CycleQ2_normalChart_character_zero_degree_at_least_three

set_option autoImplicit false
open HodgeComputer HodgeComputer.CycleQ2

theorem solution :
    (∃ (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n),
      S ≠ 0 ∧ S.IsHomogeneous 2 ∧ S.totalDegree = 2 ∧
      IsRelPrime F S ∧
      (∀ j, (W j).IsHomogeneous (2 + 7)) ∧
      Q.IsHomogeneous (2 * 2 + 4) ∧
      IsCharacter 0 (S : AmbientPoly 5) ∧
      IsCharacter 1 (Q : AmbientPoly 5) ∧
      (∀ j, IsCharacter (numeratorCharacter j) (W j : AmbientPoly 5)) ∧
      gradedLinear S W Q = gradedInhomogeneous S) ∨
    (∃ (e : ℕ) (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n),
      3 ≤ e ∧
      S ≠ 0 ∧ S.IsHomogeneous e ∧ S.totalDegree = e ∧
      IsRelPrime F S ∧
      (∀ j, (W j).IsHomogeneous (e + 7)) ∧
      Q.IsHomogeneous (2 * e + 4) ∧
      IsCharacter 0 (S : AmbientPoly 5) ∧
      IsCharacter 1 (Q : AmbientPoly 5) ∧
      (∀ j, IsCharacter (numeratorCharacter j) (W j : AmbientPoly 5)) ∧
      gradedLinear S W Q = gradedInhomogeneous S) := by
  refine Or.inr ?_
  exact HodgeComputer.CycleQ2.normalChart_character_zero_degree_at_least_three
