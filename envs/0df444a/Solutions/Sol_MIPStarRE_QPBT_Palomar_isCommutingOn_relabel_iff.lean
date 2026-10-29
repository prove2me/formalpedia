-- Prove2me | solution 1 for MIPStarRE.QPBT.Palomar.isCommutingOn_relabel_iff
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:51:21.124953+00:00
-- url     : https://prove2.me/submissions/82875082-a295-4e7b-bdea-71c487cc9250

-- Generated proof for MIPStarRE.QPBT.Palomar.isCommutingOn_relabel_iff.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_QPBT_QPBT_Palomar_Definitions
import Definitions.Def_QPBT_QPBT_Palomar_LowDegreeGameStrategyBridge
import Definitions.Def_QPBT_QPBT_Palomar_PauliGameStrategyBridge
import Mathlib

namespace MIPStarRE.QPBT.Palomar
end MIPStarRE.QPBT.Palomar
namespace MIPStarRE.QPBT.Palomar.Game
end MIPStarRE.QPBT.Palomar.Game
namespace MIPStarRE.QPBT.Palomar.PMF
end MIPStarRE.QPBT.Palomar.PMF
namespace MIPStarRE.QPBT.Palomar.POVM
end MIPStarRE.QPBT.Palomar.POVM
namespace MIPStarRE.QPBT.Palomar.SymmetricGame
end MIPStarRE.QPBT.Palomar.SymmetricGame
namespace MIPStarRE.QPBT.Palomar.SymmetricStrategy
end MIPStarRE.QPBT.Palomar.SymmetricStrategy

/-!
# Strategy bridge for the compact Pauli basis game

This module transports compact strategies across the exact question and answer
equivalences of `PauliGameBridge`.  It preserves the game, Born value,
projectivity, symmetry, consistency, positive-support commutation, and the SPCC
predicate exactly.

## References

`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1126-1491`.
-/



open MIPStarRE.QPBT.Palomar





open MIPStarRE.QPBT.Palomar.PMF







open MIPStarRE.QPBT.Palomar.POVM
attribute [local instance] _root_.MIPStarRE.QPBT.Palomar.compactPauliQuestionDecidableEq

theorem solution
    {X Y A B X' Y' A' B' I : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
    [Fintype I] [DecidableEq I]
    (μ : PMF (X × Y)) (alice : X → _root_.MIPStarRE.QPBT.Palomar.POVM A I) (bob : Y → _root_.MIPStarRE.QPBT.Palomar.POVM B I)
    (eX : X ≃ X') (eY : Y ≃ Y') (eA : A ≃ A') (eB : B ≃ B') :
    _root_.MIPStarRE.QPBT.Palomar.IsCommutingOn (μ.map (Equiv.prodCongr eX eY))
        (fun x => _root_.MIPStarRE.QPBT.Palomar.POVM.relabel eA (alice (eX.symm x)))
        (fun y => _root_.MIPStarRE.QPBT.Palomar.POVM.relabel eB (bob (eY.symm y))) ↔
      _root_.MIPStarRE.QPBT.Palomar.IsCommutingOn μ alice bob := by
  constructor
  · intro h x y hxy a b
    have hxy' : 0 < (μ.map (Equiv.prodCongr eX eY)) (eX x, eY y) := by
      rw [show (eX x, eY y) = (Equiv.prodCongr eX eY) (x, y) by rfl]
      simpa only [_root_.MIPStarRE.QPBT.Palomar.PMF.map_equiv_apply] using hxy
    simpa using h (eX x) (eY y) hxy' (eA a) (eB b)
  · intro h x y hxy a b
    have hxy' : 0 < μ (eX.symm x, eY.symm y) := by
      rw [_root_.MIPStarRE.QPBT.Palomar.PMF.map_equiv_apply'] at hxy
      simpa using hxy
    simpa using h (eX.symm x) (eY.symm y) hxy' (eA.symm a) (eB.symm b)
