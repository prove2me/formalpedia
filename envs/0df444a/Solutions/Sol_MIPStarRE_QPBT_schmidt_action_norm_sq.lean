-- Prove2me | solution 1 for MIPStarRE.QPBT.schmidt_action_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:45:51.354982+00:00
-- url     : https://prove2.me/submissions/0bb4487e-fb63-4299-ac57-809356484c17

-- Generated proof for MIPStarRE.QPBT.schmidt_action_norm_sq.
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
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Pasting_SchmidtMirror

namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-! # State-dependent Schmidt mirrors

This module constructs the opposite-register mirror used in the one-sided
pasting argument. The auxiliary construction uses the spectral theorem and
orthonormal completion, including zero Schmidt coefficients.

## References

`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`, `lem:pasting`;
`docs/paper-gaps/qpbt_pasting-product-error.tex`, issue Dengnifer/MIPStarRE-QPBT-bak#201. The
Schmidt-mirror
argument is a formalization auxiliary, not an additional paper hypothesis.
-/



open scoped BigOperators MatrixOrder Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective











variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem solution (ψ : EuclideanSpace ℂ (ι × ι)) (alice bob : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron alice 1) ψ -
      _root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron 1 bob) ψ‖ ^ 2 =
      ∑ row, ∑ col, Complex.normSq
        ((alice * _root_.MIPStarRE.QPBT.schmidtCoefficientMatrix ψ - _root_.MIPStarRE.QPBT.schmidtCoefficientMatrix ψ * bobᵀ) row col) := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [Complex.sq_norm, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro row _
  apply Finset.sum_congr rfl
  intro col _
  congr 1
  simp [_root_.MIPStarRE.QPBT.applyOperatorToState, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
    Matrix.mulVec, dotProduct, _root_.MIPStarRE.QPBT.heteroKron, Matrix.kronecker,
    Fintype.sum_prod_type, Matrix.mul_apply, _root_.MIPStarRE.QPBT.schmidtCoefficientMatrix,
    Matrix.one_apply, ite_mul, mul_ite, mul_comm]
