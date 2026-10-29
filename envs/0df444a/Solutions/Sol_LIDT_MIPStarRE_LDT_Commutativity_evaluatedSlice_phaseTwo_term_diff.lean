-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlice_phaseTwo_term_diff
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T13:57:21.80705+00:00
-- url     : https://prove2.me/submissions/599ea7fc-81c4-4318-bb5a-ca53b1d632e1

-- Generated proof for MIPStarRE.LDT.Commutativity.evaluatedSlice_phaseTwo_term_diff.
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

/- Source helpers from MIPStarRE/LDT/Commutativity/ScalarApproximation/PaperChainBasic/Reindexing.lean. -/
/-!
# Reindexing and evaluation utilities for the evaluated-slice paper chain

This file contains finite-reindexing and evaluated-family identities used by
the paper-faithful scalar approximation chain.
-/

@[expose] public section

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The evaluated point family has the same total as the underlying slice
measurement `G` at the sampled height.

This unfolds `evaluatedPointFamily` as postprocessing of `family.meas y`; the
postprocessing total is unchanged, and `hG` identifies the slice with `G y`. -/
lemma evaluatedPointFamily_total_eq_G_total
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (u : Point params.next) :
    ((evaluatedPointFamily params family u).total) =
      (G (pointHeight params u)).total := by
  simp [evaluatedPointFamily, IdxPolyFamily.evaluatedAtNextPoint, evaluateAt,
    postprocess_total, hG]






end MIPStarRE.LDT.Commutativity

end

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
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (q : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params)
    (a b : _root_.LIDT.MIPStarRE.LDT.Fq params) :
    _root_.LIDT.MIPStarRE.LDT.ev strategy.state
        (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
            (((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a) *
              ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceSecondFactor params family q).outcome b) *
              ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a)) *
          ((_root_.LIDT.MIPStarRE.LDT.Preliminaries.totalSandwichFamily
            (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamily params family)
            (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy) q.2).outcome b)) -
      _root_.LIDT.MIPStarRE.LDT.ev strategy.state
        (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
            (((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a) *
              ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceSecondFactor params family q).outcome b) *
              ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a)) *
          _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.2).outcome b)) =
    - _root_.LIDT.MIPStarRE.LDT.ev strategy.state
        (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
            ((((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a) *
              ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceSecondFactor params family q).outcome b) *
              ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a)) *
              (1 - (G (_root_.LIDT.MIPStarRE.LDT.pointHeight params q.2)).total)) *
          _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.2).outcome b)) := by
  have htotal := _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamily_total_eq_G_total params family G hG q.2
  let S : _root_.LIDT.MIPStarRE.Quantum.Op ι :=
    ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a) *
      ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceSecondFactor params family q).outcome b) *
      ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a)
  let T : _root_.LIDT.MIPStarRE.Quantum.Op ι := (G (_root_.LIDT.MIPStarRE.LDT.pointHeight params q.2)).total
  let P : _root_.LIDT.MIPStarRE.Quantum.Op ι := (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.2).outcome b
  change
    _root_.LIDT.MIPStarRE.LDT.ev strategy.state
        (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) S *
          ((_root_.LIDT.MIPStarRE.LDT.Preliminaries.totalSandwichFamily
            (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamily params family)
            (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy) q.2).outcome b)) -
      _root_.LIDT.MIPStarRE.LDT.ev strategy.state
        (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) S * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) P) =
    - _root_.LIDT.MIPStarRE.LDT.ev strategy.state
        (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (S * (1 - T)) * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) P)
  rw [show ((_root_.LIDT.MIPStarRE.LDT.Preliminaries.totalSandwichFamily
            (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamily params family)
            (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy) q.2).outcome b) =
        _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) P by
          simp [_root_.LIDT.MIPStarRE.LDT.Preliminaries.totalSandwichFamily, htotal, T, P]]
  rw [← _root_.LIDT.MIPStarRE.LDT.ev_sub]
  have hop :
      _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) S * (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) P) -
          _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) S * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) P =
        -(_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (S * (1 - T)) * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) P) := by
    calc
      _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) S * (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) P) -
          _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) S * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) P
        = (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) S * _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T) *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) P -
            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) S * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) P := by
              rw [mul_assoc]
      _ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (S * T) * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) P -
            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) S * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) P := by
              rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_mul_leftTensor]
      _ = _root_.LIDT.MIPStarRE.LDT.opTensor (S * T) P - _root_.LIDT.MIPStarRE.LDT.opTensor S P := by
              rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor,
                _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor]
      _ = _root_.LIDT.MIPStarRE.LDT.opTensor (S * T - S) P := by
              rw [_root_.LIDT.MIPStarRE.LDT.opTensor_sub_left]
      _ = _root_.LIDT.MIPStarRE.LDT.opTensor (-(S * (1 - T))) P := by
              have hs : S * T - S = -(S * (1 - T)) := by noncomm_ring
              rw [hs]
      _ = -(_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (S * (1 - T)) * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) P) := by
              have hneg : _root_.LIDT.MIPStarRE.LDT.opTensor (-(S * (1 - T))) P = -(_root_.LIDT.MIPStarRE.LDT.opTensor (S * (1 - T)) P) := by
                simpa [_root_.LIDT.MIPStarRE.LDT.opTensor] using
                  (Matrix.smul_kronecker (-1 : ℂ) (S * (1 - T)) P)
              rw [hneg]
              rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor]
  rw [hop]
  simpa using
    (_root_.LIDT.MIPStarRE.LDT.ev_scale strategy.state (-1)
      (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (S * (1 - T)) * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) P))
