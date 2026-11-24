-- Prove2me | solution 1 for HodgeComputer.CycleQ2.normalChart_character_zero_degree_three_X2_cubed
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T17:02:01.972751+00:00
-- url     : https://prove2.me/submissions/a51573ec-217c-457c-80a1-218c6b84b1fc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_HodgeComputerCycleQ2
import Definitions.Def_HodgeComputerNormalChart
import Definitions.Def_HodgeComputerCycleQ2SparseSource
import Definitions.Def_HodgeComputerCycleQ2ChartDivergence
import Definitions.Def_HodgeComputerCycleQ2GradedLinear
import Definitions.Def_HodgeComputerCycleQ2Character
import Definitions.Def_HodgeComputerCycleQ2NumeratorCharacter
import Theorems.Thm_HodgeComputer_CycleQ2_normalChart_X2_cubed_denominator_legal
import Theorems.Thm_HodgeComputer_CycleQ2_normalChart_X2_cubed_linear_system

set_option autoImplicit false
open HodgeComputer HodgeComputer.CycleQ2

theorem solution :
    ∃ (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n),
      S = (MvPolynomial.X (R := ℂ) (2 : Fin 6)) ^ (3 : ℕ) ∧
      S ≠ 0 ∧ S.IsHomogeneous 3 ∧ S.totalDegree = 3 ∧
      IsRelPrime F S ∧
      (∀ j, (W j).IsHomogeneous (3 + 7)) ∧
      Q.IsHomogeneous (2 * 3 + 4) ∧
      IsCharacter 0 (S : AmbientPoly 5) ∧
      IsCharacter 1 (Q : AmbientPoly 5) ∧
      (∀ j, IsCharacter (numeratorCharacter j) (W j : AmbientPoly 5)) ∧
      gradedLinear S W Q = gradedInhomogeneous S := by
  let S : AmbientPoly n := (MvPolynomial.X (R := ℂ) (2 : Fin 6)) ^ (3 : ℕ)
  rcases HodgeComputer.CycleQ2.normalChart_X2_cubed_denominator_legal with
    ⟨hne, hhom, htd, hrp, hchi⟩
  obtain ⟨W, Q, hW, hQhom, hQ1, hWn, hlin⟩ :=
    HodgeComputer.CycleQ2.normalChart_X2_cubed_linear_system
  exact ⟨S, W, Q, rfl, hne, hhom, htd, hrp, hW, hQhom, hchi, hQ1, hWn, hlin⟩
