-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.CommutativityPoints.qSDDOp_reindex
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T14:08:57.55695+00:00
-- url     : https://prove2.me/submissions/973e8ff0-fbaa-4892-89e9-486723a02f2f

-- Generated proof for MIPStarRE.LDT.CommutativityPoints.qSDDOp_reindex.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_MeasurementLift
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFUniformAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Approximation
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Core
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

open scoped _root_.Matrix

namespace LIDT.MIPStarRE.LDT.CommutativityPoints
end LIDT.MIPStarRE.LDT.CommutativityPoints

namespace LIDT

end LIDT

open LIDT
/-!
# Section 10 commutativity points: shared helpers core

Shared reindexing and tensor-placement helpers used by the Section 10
commutativity-of-points argument.

## References

- `references/ldt-paper/commutativity-points.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.CommutativityPoints

open MIPStarRE.LDT.GlobalVariance (PointPairQuestion)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped _root_.Matrix MatrixOrder ComplexOrder BigOperators
/-! ## Shared reindexing and tensor-placement helpers -/

theorem solution
    {Outcome Outcome' : Type*}
    [Fintype Outcome] [Fintype Outcome']
    (e : Outcome ≃ Outcome')
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState ι)
    (A B : _root_.LIDT.MIPStarRE.LDT.OpFamily Outcome ι) :
    _root_.LIDT.MIPStarRE.LDT.qSDDOp ψ A B =
      _root_.LIDT.MIPStarRE.LDT.qSDDOp ψ
        ({ outcome := fun a' => A.outcome (e.symm a')
           total := A.total } : _root_.LIDT.MIPStarRE.LDT.OpFamily Outcome' ι)
        ({ outcome := fun a' => B.outcome (e.symm a')
           total := B.total } : _root_.LIDT.MIPStarRE.LDT.OpFamily Outcome' ι) := by
  unfold _root_.LIDT.MIPStarRE.LDT.qSDDOp _root_.LIDT.MIPStarRE.LDT.qSDDCore
  calc
    ∑ a : Outcome, _root_.LIDT.MIPStarRE.LDT.ev ψ ((A.outcome a - B.outcome a)ᴴ * (A.outcome a - B.outcome a))
      = ∑ a' : Outcome',
          _root_.LIDT.MIPStarRE.LDT.ev ψ
            ((A.outcome (e.symm a') - B.outcome (e.symm a'))ᴴ *
              (A.outcome (e.symm a') - B.outcome (e.symm a'))) := by
          exact Fintype.sum_equiv e
            (fun a =>
              _root_.LIDT.MIPStarRE.LDT.ev ψ ((A.outcome a - B.outcome a)ᴴ * (A.outcome a - B.outcome a)))
            (fun a' =>
              _root_.LIDT.MIPStarRE.LDT.ev ψ
                ((A.outcome (e.symm a') - B.outcome (e.symm a'))ᴴ *
                  (A.outcome (e.symm a') - B.outcome (e.symm a'))))
            (by
              intro a
              simp)
    _ = _root_.LIDT.MIPStarRE.LDT.qSDDOp ψ
          ({ outcome := fun a' => A.outcome (e.symm a')
             total := A.total } : _root_.LIDT.MIPStarRE.LDT.OpFamily Outcome' ι)
          ({ outcome := fun a' => B.outcome (e.symm a')
             total := B.total } : _root_.LIDT.MIPStarRE.LDT.OpFamily Outcome' ι) := by
          rfl
