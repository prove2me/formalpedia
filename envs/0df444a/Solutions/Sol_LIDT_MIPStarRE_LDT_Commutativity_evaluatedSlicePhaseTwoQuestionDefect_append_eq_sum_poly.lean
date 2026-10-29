-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseTwoQuestionDefect_append_eq_sum_poly
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T13:57:21.615961+00:00
-- url     : https://prove2.me/submissions/dea414f8-d5ed-4059-b64f-2d0dd2acb188

-- Generated proof for MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseTwoQuestionDefect_append_eq_sum_poly.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_SharedHelpers_SharedLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Normalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Stability
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_EvaluatedSliceBounds_PhaseOneThree
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_GCommStability_Scalar_First
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Products
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_ProcessedG_PhaseTwo
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Local
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
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
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Theorems.Thm_LIDT_MIPStarRE_LDT_Commutativity_ev_leftTensor_mul_middle_finset_sum

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Commutativity
end LIDT.MIPStarRE.LDT.Commutativity
namespace LIDT.MIPStarRE.LDT.Commutativity.GCommStability.Scalar
end LIDT.MIPStarRE.LDT.Commutativity.GCommStability.Scalar
namespace LIDT.MIPStarRE.LDT.CommutativityPoints
end LIDT.MIPStarRE.LDT.CommutativityPoints
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

namespace LIDT

end LIDT

open LIDT
/-!
# Phase 2 stability defect infrastructure

Internal helper definitions and lemmas for the Phase 2 scalar bridge in
`ProcessedG`.  These definitions extract and bound the one-dimensional stability
defect controlled by `gCommStability_scalar` (the paper's `clm:g-comm-stability`),
reindex the question-level defect into the stability defect via finite
marginalization, and perform the subtraction algebra that rewrites the phase-2
insertion/removal difference as the negative defect.
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
    (strategy : _root_.LIDT.MIPStarRE.LDT.SymStrat params.next ι)
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    (G : _root_.LIDT.MIPStarRE.LDT.Fq params → _root_.LIDT.MIPStarRE.LDT.SubMeas (_root_.LIDT.MIPStarRE.LDT.Polynomial params) ι)
    (q1 : _root_.LIDT.MIPStarRE.LDT.Point params.next) (v : _root_.LIDT.MIPStarRE.LDT.Point params) (y : _root_.LIDT.MIPStarRE.LDT.Fq params) :
    _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseTwoQuestionDefect params strategy family G
        (q1, _root_.LIDT.MIPStarRE.LDT.appendPoint params v y) =
      ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params,
        _root_.LIDT.MIPStarRE.LDT.ev strategy.state
          (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
              ((((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamily params family q1).outcome a) *
                ((family.meas y).toSubMeas.outcome g) *
                ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamily params family q1).outcome a)) *
                (1 - (G y).total)) *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
              ((strategy.pointMeasurement (_root_.LIDT.MIPStarRE.LDT.appendPoint params v y)).outcome (g v))) := by
  classical
  let E : _root_.LIDT.MIPStarRE.LDT.Fq params → _root_.LIDT.MIPStarRE.Quantum.Op ι :=
    fun a => (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamily params family q1).outcome a
  let Y : _root_.LIDT.MIPStarRE.LDT.Polynomial params → _root_.LIDT.MIPStarRE.Quantum.Op ι :=
    fun g => ((family.meas y).toSubMeas.outcome g)
  let P : _root_.LIDT.MIPStarRE.LDT.Fq params → _root_.LIDT.MIPStarRE.Quantum.Op ι :=
    fun b => (strategy.pointMeasurement (_root_.LIDT.MIPStarRE.LDT.appendPoint params v y)).outcome b
  let R : _root_.LIDT.MIPStarRE.Quantum.Op ι := 1 - (G y).total
  have hcollapse :
      (∑ b : _root_.LIDT.MIPStarRE.LDT.Fq params, ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params,
        _root_.LIDT.MIPStarRE.LDT.ev strategy.state
          (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
              (((E a * (∑ g ∈ (Finset.univ : Finset (_root_.LIDT.MIPStarRE.LDT.Polynomial params)).filter
                  (fun g => g v = b), Y g) * E a) * R)) *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (P b))) =
      ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params,
        _root_.LIDT.MIPStarRE.LDT.ev strategy.state
          (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (((E a * Y g * E a) * R)) *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (P (g v))) := by
    calc
      (∑ b : _root_.LIDT.MIPStarRE.LDT.Fq params, ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params,
        _root_.LIDT.MIPStarRE.LDT.ev strategy.state
          (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
              (((E a * (∑ g ∈ (Finset.univ : Finset (_root_.LIDT.MIPStarRE.LDT.Polynomial params)).filter
                  (fun g => g v = b), Y g) * E a) * R)) *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (P b)))
          = ∑ b : _root_.LIDT.MIPStarRE.LDT.Fq params, ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params,
              ∑ g ∈ (Finset.univ : Finset (_root_.LIDT.MIPStarRE.LDT.Polynomial params)).filter (fun g => g v = b),
                _root_.LIDT.MIPStarRE.LDT.ev strategy.state
                  (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (((E a * Y g * E a) * R)) *
                    _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (P b)) := by
              refine Finset.sum_congr rfl ?_
              intro b _
              refine Finset.sum_congr rfl ?_
              intro a _
              rw [_root_.LIDT.MIPStarRE.LDT.Commutativity.ev_leftTensor_mul_middle_finset_sum
                (ι := ι)
                (s := (Finset.univ : Finset (_root_.LIDT.MIPStarRE.LDT.Polynomial params)).filter (fun g => g v = b))
                (ψ := strategy.state) (A := E a) (C := E a) (R := R)
                (D := P b) (B := Y)]
      _ = ∑ b : _root_.LIDT.MIPStarRE.LDT.Fq params,
            ∑ g ∈ (Finset.univ : Finset (_root_.LIDT.MIPStarRE.LDT.Polynomial params)).filter (fun g => g v = b),
              ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params,
                _root_.LIDT.MIPStarRE.LDT.ev strategy.state
                  (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (((E a * Y g * E a) * R)) *
                    _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (P b)) := by
              refine Finset.sum_congr rfl ?_
              intro b _
              rw [Finset.sum_comm]
      _ = ∑ b : _root_.LIDT.MIPStarRE.LDT.Fq params,
            ∑ g ∈ (Finset.univ : Finset (_root_.LIDT.MIPStarRE.LDT.Polynomial params)).filter (fun g => g v = b),
              ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params,
                _root_.LIDT.MIPStarRE.LDT.ev strategy.state
                  (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (((E a * Y g * E a) * R)) *
                    _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (P (g v))) := by
              refine Finset.sum_congr rfl ?_
              intro b _
              refine Finset.sum_congr rfl ?_
              intro g hg
              have hgv : g v = b := (Finset.mem_filter.mp hg).2
              rw [hgv]
      _ = ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params,
            _root_.LIDT.MIPStarRE.LDT.ev strategy.state
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (((E a * Y g * E a) * R)) *
                _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (P (g v))) := by
              simpa using
                (Finset.sum_fiberwise (Finset.univ : Finset (_root_.LIDT.MIPStarRE.LDT.Polynomial params))
                  (fun g : _root_.LIDT.MIPStarRE.LDT.Polynomial params => g v)
                  (fun g : _root_.LIDT.MIPStarRE.LDT.Polynomial params =>
                    ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params,
                      _root_.LIDT.MIPStarRE.LDT.ev strategy.state
                        (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (((E a * Y g * E a) * R)) *
                          _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (P (g v)))))
  simpa [E, Y, P, R, _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseTwoQuestionDefect,
    _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor, _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceSecondFactor, _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas,
    _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamily, _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily.evaluatedAtNextPoint, _root_.LIDT.MIPStarRE.LDT.evaluateAt,
    _root_.LIDT.MIPStarRE.LDT.postprocess, _root_.LIDT.MIPStarRE.LDT.pointHeight_appendPoint, _root_.LIDT.MIPStarRE.LDT.truncatePoint_appendPoint, _root_.LIDT.MIPStarRE.LDT.Parameters.next,
    mul_assoc] using hcollapse
