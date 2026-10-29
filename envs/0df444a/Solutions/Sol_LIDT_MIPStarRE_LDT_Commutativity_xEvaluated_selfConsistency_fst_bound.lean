-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Commutativity.xEvaluated_selfConsistency_fst_bound
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T14:05:52.059927+00:00
-- url     : https://prove2.me/submissions/28c7e255-b101-426c-964a-92548c5091cb

-- Generated proof for MIPStarRE.LDT.Commutativity.xEvaluated_selfConsistency_fst_bound.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Normalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Stability
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_EvaluatedSliceBounds_PhaseOneThree
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Products
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Averages
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_Pullback
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Local
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CompletionTransfer
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_PolynomialAgreement
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SelfConsistency_Extensions
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_ApproxDelta
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyPolynomialFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Core
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Mathlib
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.RingTheory.MvPolynomial.Basic
import Theorems.Thm_LIDT_MIPStarRE_LDT_Commutativity_evaluatedPointFamily_selfConsistency_of_stronglySelfConsistent

namespace LIDT.MIPStarRE.LDT.Commutativity
end LIDT.MIPStarRE.LDT.Commutativity
namespace LIDT.MIPStarRE.LDT.CommutativityPoints
end LIDT.MIPStarRE.LDT.CommutativityPoints
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

namespace LIDT

/- Source helpers from MIPStarRE/LDT/Commutativity/Transport/FullSlice/Averages.lean. -/
/-!
# Full-slice averages and index equivalences

Zero-family definition, shared average-reindexing helpers, and averaged scalar
and tensor quantities for the full-slice outcome space, together with
data-reindexing equivalences.

The tensor-form averages are internal to the scalar/tensor comparison recorded
in `docs/decisions/713-scalar-tensor-decision.md`; downstream code should use
the scalar public API.

## References

- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]




























/-- Averaging mixed x-evaluated data and ignoring the full-y coordinate gives the
uniform average over `Point params.next`. -/
lemma avgOver_xEvaluatedQuestion_to_pointNext
    (params : Parameters) [FieldModel params.q]
    (f : Point params.next → Error) :
    avgOver (uniformDistribution (Point params × FullSliceQuestion params))
        (fun ux => f (appendPoint params ux.1 ux.2.1)) =
      avgOver (uniformDistribution (Point params.next)) f := by
  simpa [xEvaluatedQuestionPointNextEquiv] using
    (MIPStarRE.LDT.avgOver_uniform_equiv_fst
      (e := xEvaluatedQuestionPointNextEquiv params) (f := f))





end MIPStarRE.LDT.Commutativity

end

end LIDT

open LIDT
/-!
# Full-slice normalization and self-consistency machinery

Normalization-condition bounds, evaluated projective submeasurements, and
full-slice and evaluated-slice self-consistency estimates used by the scalar-to-tensor
comparison.

The tensor-form estimates are internal to the scalar/tensor comparison recorded
in `docs/decisions/713-scalar-tensor-decision.md`; downstream code should use
the scalar public API exposed by the full-slice transport theorems.

## References

- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters) [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (strategy : _root_.LIDT.MIPStarRE.LDT.SymStrat params.next ι) (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    (zeta : _root_.LIDT.MIPStarRE.LDT.Error)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params × _root_.LIDT.MIPStarRE.LDT.Commutativity.FullSliceQuestion params))
        (fun ux =>
          _root_.LIDT.MIPStarRE.LDT.qSDDCore strategy.state
            (fun a : _root_.LIDT.MIPStarRE.LDT.Fq params => _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
              ((_root_.LIDT.MIPStarRE.LDT.evaluateAt params ux.1 ((family.meas ux.2.1).toSubMeas)).outcome a))
            (fun a : _root_.LIDT.MIPStarRE.LDT.Fq params => _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
              ((_root_.LIDT.MIPStarRE.LDT.evaluateAt params ux.1 ((family.meas ux.2.1).toSubMeas)).outcome a))) ≤
      zeta := by
  have hpoint := _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamily_selfConsistency_of_stronglySelfConsistent
    params strategy family zeta hself
  calc
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params × _root_.LIDT.MIPStarRE.LDT.Commutativity.FullSliceQuestion params))
        (fun ux =>
          _root_.LIDT.MIPStarRE.LDT.qSDDCore strategy.state
            (fun a : _root_.LIDT.MIPStarRE.LDT.Fq params => _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
              ((_root_.LIDT.MIPStarRE.LDT.evaluateAt params ux.1 ((family.meas ux.2.1).toSubMeas)).outcome a))
            (fun a : _root_.LIDT.MIPStarRE.LDT.Fq params => _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
              ((_root_.LIDT.MIPStarRE.LDT.evaluateAt params ux.1 ((family.meas ux.2.1).toSubMeas)).outcome a)))
      = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
          (fun w =>
            _root_.LIDT.MIPStarRE.LDT.qSDDCore strategy.state
              (fun a : _root_.LIDT.MIPStarRE.LDT.Fq params => _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamily params family w).outcome a))
              (fun a : _root_.LIDT.MIPStarRE.LDT.Fq params => _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
                ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamily params family w).outcome a))) := by
          simpa [_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamily, _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily.evaluatedAtNextPoint, _root_.LIDT.MIPStarRE.LDT.evaluateAt,
            _root_.LIDT.MIPStarRE.LDT.truncatePoint_appendPoint, _root_.LIDT.MIPStarRE.LDT.pointHeight_appendPoint] using
            _root_.LIDT.MIPStarRE.LDT.Commutativity.avgOver_xEvaluatedQuestion_to_pointNext params
              (fun w : _root_.LIDT.MIPStarRE.LDT.Point params.next =>
                _root_.LIDT.MIPStarRE.LDT.qSDDCore strategy.state
                  (fun a : _root_.LIDT.MIPStarRE.LDT.Fq params => _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                    ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamily params family w).outcome a))
                  (fun a : _root_.LIDT.MIPStarRE.LDT.Fq params => _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
                    ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamily params family w).outcome a)))
    _ ≤ zeta := by
          have hbound := hpoint.squaredDistanceBound
          change _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
            (fun w => _root_.LIDT.MIPStarRE.LDT.qSDDCore strategy.state
              (fun a : _root_.LIDT.MIPStarRE.LDT.Fq params =>
                _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamily params family w).outcome a))
              (fun a : _root_.LIDT.MIPStarRE.LDT.Fq params =>
                _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
                  ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamily params family w).outcome a))) ≤ zeta at hbound
          exact hbound
