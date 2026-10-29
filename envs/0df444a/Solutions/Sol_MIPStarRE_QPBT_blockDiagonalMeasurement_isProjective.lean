-- Prove2me | solution 1 for MIPStarRE.QPBT.blockDiagonalMeasurement_isProjective
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:28:22.590817+00:00
-- url     : https://prove2.me/submissions/dc726579-5a9d-4a29-92c2-f10dcdbc8799

-- Generated proof for MIPStarRE.QPBT.blockDiagonalMeasurement_isProjective.
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
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_SeedFiber
import Definitions.Def_QPBT_QPBT_Games_Defs
import Mathlib

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# Seed-fiber dilation for the directly indexed low-degree game

This module dilates a seed-indexed low-degree strategy by a maximally
correlated residue register.  Block-diagonal projective measurements retain
arbitrary dependence on the seed within each `chiIndex` fiber.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-458`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/



open scoped BigOperators MatrixOrder Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.Quantum



/-! ## Projective block measurements -/

theorem solution
    {alpha iota block : Type*}
    [Fintype alpha] [Fintype iota] [DecidableEq iota]
    [Fintype block] [DecidableEq block]
    (M : block → _root_.LIDT.MIPStarRE.Quantum.Measurement alpha iota)
    (hM : ∀ r, _root_.MIPStarRE.QPBT.Measurement.IsProjective (M r)) :
    _root_.MIPStarRE.QPBT.Measurement.IsProjective (_root_.MIPStarRE.QPBT.blockDiagonalMeasurement M) := by
  intro a
  constructor
  · change Matrix.blockDiagonal (fun r => (M r).effect a) *
        Matrix.blockDiagonal (fun r => (M r).effect a) =
      Matrix.blockDiagonal (fun r => (M r).effect a)
    rw [← Matrix.blockDiagonal_mul]
    congr 1
    funext r
    exact (hM r a).isIdempotentElem.eq
  · change (Matrix.blockDiagonal (fun r => (M r).effect a))ᴴ =
      Matrix.blockDiagonal (fun r => (M r).effect a)
    rw [Matrix.blockDiagonal_conjTranspose]
    congr 1
    funext r
    exact (hM r a).isSelfAdjoint.star_eq
