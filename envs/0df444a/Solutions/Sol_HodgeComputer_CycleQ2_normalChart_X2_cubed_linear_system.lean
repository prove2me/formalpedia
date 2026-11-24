-- Prove2me | solution 1 for HodgeComputer.CycleQ2.normalChart_X2_cubed_linear_system
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T18:02:13.214356+00:00
-- url     : https://prove2.me/submissions/5ad4493b-841d-4e5e-aeaf-024a2ae78526
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
import Theorems.Thm_HodgeComputer_CycleQ2_normalChart_denomX2Cubed_linear_system

set_option autoImplicit false
open HodgeComputer HodgeComputer.CycleQ2

theorem solution :
    ∃ (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n),
      (∀ j, (W j).IsHomogeneous (3 + 7)) ∧
      Q.IsHomogeneous (2 * 3 + 4) ∧
      IsCharacter 1 (Q : AmbientPoly 5) ∧
      (∀ j, IsCharacter (numeratorCharacter j) (W j : AmbientPoly 5)) ∧
      gradedLinear ((MvPolynomial.X (R := ℂ) (2 : Fin 6)) ^ (3 : ℕ)) W Q =
        gradedInhomogeneous ((MvPolynomial.X (R := ℂ) (2 : Fin 6)) ^ (3 : ℕ)) := by
  obtain ⟨W, Q, hW, hQhom, hQ1, hWn, hlin⟩ :=
    HodgeComputer.CycleQ2.normalChart_denomX2Cubed_linear_system
  refine ⟨W, Q, hW, hQhom, hQ1, hWn, ?_⟩
  simpa [denomX2Cubed] using hlin
