-- Prove2me | solution 1 for HodgeComputer.CycleQ2.normalChart_denomX2Cubed_carrier_system
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T22:52:07.857306+00:00
-- url     : https://prove2.me/submissions/88b2bf36-68e2-400c-92d7-a4b7877114fd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_HodgeComputerCycleQ2
import Definitions.Def_HodgeComputerNormalChart
import Definitions.Def_HodgeComputerCycleQ2SparseSource
import Definitions.Def_HodgeComputerCycleQ2ChartDivergence
import Definitions.Def_HodgeComputerCycleQ2GradedLinear
import Definitions.Def_HodgeComputerCycleQ2Character
import Definitions.Def_HodgeComputerCycleQ2NumeratorCharacter
import Definitions.Def_HodgeComputerCycleQ2DenomX2Cubed
import Theorems.Thm_HodgeComputer_CycleQ2_normalChart_denomX2Cubed_carrier_homogeneous
import Theorems.Thm_HodgeComputer_CycleQ2_normalChart_denomX2Cubed_carrier_character_lift

set_option autoImplicit false
open HodgeComputer HodgeComputer.CycleQ2

theorem solution :
    ∃ (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n),
      (∀ j, (W j).IsHomogeneous (3 + 7)) ∧
      Q.IsHomogeneous (2 * 3 + 4) ∧
      IsCharacter 1 (Q : AmbientPoly 5) ∧
      (∀ j, IsCharacter (numeratorCharacter j) (W j : AmbientPoly 5)) ∧
      divergenceCarrier denomX2Cubed W = (F : AmbientPoly n) ^ 2 * Q := by
  obtain ⟨W, Q, hW, hQ, heq⟩ :=
    HodgeComputer.CycleQ2.normalChart_denomX2Cubed_carrier_homogeneous
  exact HodgeComputer.CycleQ2.normalChart_denomX2Cubed_carrier_character_lift W Q hW hQ heq
