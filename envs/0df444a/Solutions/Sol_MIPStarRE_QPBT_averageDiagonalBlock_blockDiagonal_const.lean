-- Prove2me | solution 1 for MIPStarRE.QPBT.averageDiagonalBlock_blockDiagonal_const
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:25:06.428503+00:00
-- url     : https://prove2.me/submissions/f64aaabe-d702-423e-821c-02d414bd1d18

-- Generated proof for MIPStarRE.QPBT.averageDiagonalBlock_blockDiagonal_const.
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
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Consistency_Measurements
import Mathlib

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# The point-agreement branch as a consistency estimate

The low-degree game asks both players a point question in one of its nine
ordered type branches and accepts only equal point answers.  This module reads
that branch as a quantitative consistency relation between the two point
readouts, first for the directly indexed game and then, through the correlated
seed-residue dilation, for the seed-indexed game.

The estimate is the third input, besides the two conclusions of the low
individual degree theorem, from which the global polynomial relation of
`lem:ld-soundness` is obtained after the seed-residue ancilla has been
compressed away: the compressed polynomial measurements are consistent with
the point measurements of the *opposite* player only, and the point-agreement
branch is what links the two point measurements to each other.

## Main results

* `directLdPointPair_consistencyDefect_le` bounds the point-readout
  consistency defect of a direct strategy of value at least `1 - ε` by
  `9 ε`, the loss being the uniform weight of one of the nine ordered type
  branches.
* `ldPointPair_consistencyDefect_le` is the same estimate for the
  seed-indexed game, obtained from the direct one because the point
  measurements of the dilated strategy act trivially on the correlated
  residue register.

## References

* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:137-167`
* `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/



open scoped BigOperators MatrixOrder Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.Quantum



/-! ## The point-agreement branch of the directly indexed game -/











/-! ## Transport through the correlated seed-residue dilation -/

theorem solution
    {iota block : Type*} [Fintype iota]
    [Fintype block] [DecidableEq block] [Nonempty block] (M : _root_.LIDT.MIPStarRE.Quantum.Op iota) :
    _root_.MIPStarRE.QPBT.averageDiagonalBlock (Matrix.blockDiagonal fun _ : block => M) = M := by
  classical
  have hsub : ∀ r : block,
      (Matrix.blockDiagonal fun _ : block => M).submatrix
        (fun i => (i, r)) (fun i => (i, r)) = M := by
    intro r
    ext i j
    simp [Matrix.blockDiagonal_apply_eq]
  have hcard : ((Fintype.card block : ℝ)) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero (α := block))
  unfold _root_.MIPStarRE.QPBT.averageDiagonalBlock
  simp only [hsub, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hcard, one_smul]
