-- Prove2me | solution 1 for MIPStarRE.QPBT.WinImplications.norm_product_transfer_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:04:37.995045+00:00
-- url     : https://prove2.me/submissions/6bef56f5-d061-4d3c-a954-b2f2892171d8

-- Generated proof for MIPStarRE.QPBT.WinImplications.norm_product_transfer_le.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_GroundSlice
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Reflections
import Mathlib

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

/-!
# Approximate anticommutation of the point observables on anticommuting tuples

This module carries out the anticommuting half of the proof of Equation
`eq:pts-obs-commutation` in `lem:qld-win-implications-obs`. The Magic Square
approximate anticommutation of the variable observables is read back from the
projective dilation on which it is proved, and transported to Alice's point
observables through item 7 of `lem:qld-win-implications`.

## References

The declarations support `lem:qld-win-implications-obs` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:761-794`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:342-362`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum



open MIPStarRE.QPBT.WinImplications

/-! ## Reading the dilation back on the original space -/













/-! ## The Magic Square anticommutation on the undilated strategy -/













/-! ## Reflections and the product transfer -/

theorem solution {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB] (A C : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (B D : _root_.LIDT.MIPStarRE.Quantum.Op ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB))
    (hA : (_root_.MIPStarRE.QPBT.heteroKron A (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιB))ᴴ * _root_.MIPStarRE.QPBT.heteroKron A 1 = 1)
    (hD : (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιA) D)ᴴ * _root_.MIPStarRE.QPBT.heteroKron 1 D = 1) :
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState
        (_root_.MIPStarRE.QPBT.heteroKron (A * C) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιB) - _root_.MIPStarRE.QPBT.heteroKron 1 (D * B)) ψ‖ ≤
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState
        (_root_.MIPStarRE.QPBT.heteroKron C (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιB) - _root_.MIPStarRE.QPBT.heteroKron 1 D) ψ‖ +
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState
        (_root_.MIPStarRE.QPBT.heteroKron A (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιB) - _root_.MIPStarRE.QPBT.heteroKron 1 B) ψ‖ := by
  have hsplit : _root_.MIPStarRE.QPBT.heteroKron (A * C) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιB) - _root_.MIPStarRE.QPBT.heteroKron 1 (D * B) =
      _root_.MIPStarRE.QPBT.heteroKron A 1 * (_root_.MIPStarRE.QPBT.heteroKron C (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιB) - _root_.MIPStarRE.QPBT.heteroKron 1 D) +
        _root_.MIPStarRE.QPBT.heteroKron 1 D * (_root_.MIPStarRE.QPBT.heteroKron A (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιB) - _root_.MIPStarRE.QPBT.heteroKron 1 B) := by
    rw [mul_sub, mul_sub, _root_.MIPStarRE.QPBT.heteroKron_mul, _root_.MIPStarRE.QPBT.heteroKron_mul, _root_.MIPStarRE.QPBT.heteroKron_mul,
      _root_.MIPStarRE.QPBT.heteroKron_mul]
    simp only [mul_one, one_mul]
    abel
  rw [hsplit, _root_.MIPStarRE.QPBT.MagicSquareRigidity.applyOperatorToState_add_op]
  refine le_trans (norm_add_le _ _) ?_
  rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.norm_applyOperatorToState_isometry_mul hA,
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.norm_applyOperatorToState_isometry_mul hD]
