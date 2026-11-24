-- Prove2me | solution 1 for HodgeComputer.CycleQ2.normalChart_character_zero_weighted_numerators_at_degree
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T01:17:25.342852+00:00
-- url     : https://prove2.me/submissions/86306c55-5f51-4e3f-802b-e73e2fe4bc40
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_HodgeComputerCycleQ2
import Definitions.Def_HodgeComputerNormalChart
import Definitions.Def_HodgeComputerCycleQ2SparseSource
import Definitions.Def_HodgeComputerCycleQ2ChartDivergence
import Definitions.Def_HodgeComputerCycleQ2GradedLinear
import Definitions.Def_HodgeComputerCycleQ2Character
import Definitions.Def_HodgeComputerCycleQ2NumeratorCharacter
import Theorems.Thm_HodgeComputer_CycleQ2_normalChart_character_zero_degree_case_split

set_option autoImplicit false
open HodgeComputer HodgeComputer.CycleQ2

theorem solution :
    ∃ (e : ℕ) (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n),
      2 ≤ e ∧
      S ≠ 0 ∧ S.IsHomogeneous e ∧ S.totalDegree = e ∧
      IsRelPrime F S ∧
      (∀ j, (W j).IsHomogeneous (e + 7)) ∧
      Q.IsHomogeneous (2 * e + 4) ∧
      IsCharacter 0 (S : AmbientPoly 5) ∧
      IsCharacter 1 (Q : AmbientPoly 5) ∧
      (∀ j, IsCharacter (numeratorCharacter j) (W j : AmbientPoly 5)) ∧
      gradedLinear S W Q = gradedInhomogeneous S := by
  cases HodgeComputer.CycleQ2.normalChart_character_zero_degree_case_split with
  | inl h =>
    obtain ⟨S, W, Q, hS, hShom, hdegEq, hFS, hW, hQhom, hS0, hQ1, hWn, hchild⟩ := h
    refine ⟨2, S, W, Q, ?_, hS, hShom, hdegEq, hFS, hW, hQhom, hS0, hQ1, hWn, hchild⟩
    norm_num
  | inr h =>
    obtain ⟨e, S, W, Q, he, hS, hShom, hdegEq, hFS, hW, hQhom, hS0, hQ1, hWn, hchild⟩ := h
    refine ⟨e, S, W, Q, ?_, hS, hShom, hdegEq, hFS, hW, hQhom, hS0, hQ1, hWn, hchild⟩
    exact le_trans (by norm_num : 2 ≤ 3) he
