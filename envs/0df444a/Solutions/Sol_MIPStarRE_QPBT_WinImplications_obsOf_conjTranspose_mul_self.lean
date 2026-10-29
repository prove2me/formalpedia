-- Prove2me | solution 1 for MIPStarRE.QPBT.WinImplications.obsOf_conjTranspose_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:04:37.90186+00:00
-- url     : https://prove2.me/submissions/2501ca65-8e52-48bb-8cb3-4091f5a11943

-- Generated proof for MIPStarRE.QPBT.WinImplications.obsOf_conjTranspose_mul_self.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Basic
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

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement (ZMod 2) ι)
    (hM : _root_.MIPStarRE.QPBT.Measurement.IsProjective M) :
    (_root_.MIPStarRE.QPBT.obsOf M)ᴴ * _root_.MIPStarRE.QPBT.obsOf M = 1 := by
  have hsum : M.effect 0 + M.effect 1 = 1 := by
    have := M.sum_eq_one
    rwa [_root_.MIPStarRE.QPBT.sum_zmod_two] at this
  have h01 : M.effect 0 * M.effect 1 = 0 :=
    _root_.MIPStarRE.QPBT.DistanceCalculus.projective_effect_mul_effect_eq_zero M hM (by decide)
  have h10 : M.effect 1 * M.effect 0 = 0 :=
    _root_.MIPStarRE.QPBT.DistanceCalculus.projective_effect_mul_effect_eq_zero M hM (by decide)
  have hherm : (_root_.MIPStarRE.QPBT.obsOf M)ᴴ = _root_.MIPStarRE.QPBT.obsOf M := by
    rw [_root_.MIPStarRE.QPBT.obsOf, Matrix.conjTranspose_sub]
    rw [(Matrix.nonneg_iff_posSemidef.mp (M.pos 0)).isHermitian.eq,
      (Matrix.nonneg_iff_posSemidef.mp (M.pos 1)).isHermitian.eq]
  rw [hherm, _root_.MIPStarRE.QPBT.obsOf, sub_mul, mul_sub, mul_sub, h01, h10,
    (hM 0).isIdempotentElem.eq, (hM 1).isIdempotentElem.eq]
  rw [sub_zero, zero_sub, sub_neg_eq_add]
  exact hsum
