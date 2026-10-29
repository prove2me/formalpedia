-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlice_phaseFivePaper_avg_diff_eq_neg_orderedDefect
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T13:54:09.732468+00:00
-- url     : https://prove2.me/submissions/e30fa228-6aae-4051-92c3-a24d7f8c4024

-- Generated proof for MIPStarRE.LDT.Commutativity.evaluatedSlice_phaseFivePaper_avg_diff_eq_neg_orderedDefect.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_GCommStability_Scalar_RawSecond
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Products
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_PaperChainPhaseFive
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

/- Source helpers from MIPStarRE/LDT/Commutativity/ScalarApproximation/PaperChainPhaseFive.lean. -/
/-!
# Phase-five endpoint for the evaluated-slice paper chain

This file isolates the paper line-87 removal endpoint and the finite
reindexing to the raw scalar `G`-commutativity stability defect.
-/

@[expose] public section

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Paper-faithful phase-five removal after the right-register swap -/















/-- Pointwise algebra for the paper phase-five removal.

The swapped phase-four endpoint contains the left factor
`A_a B_b G^x.total`; subtracting the line-87 removed endpoint gives the negative
of the ordered defect `A_a B_b (1-G^x.total)`. -/
private lemma evaluatedSlice_phaseFivePaper_term_diff
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (q : EvaluatedSliceQuestion params)
    (a b : Fq params) :
    ev strategy.state
        (leftTensor (ι₂ := ι)
            (((evaluatedSliceFirstFactor params family q).outcome a) *
              ((evaluatedSliceSecondFactor params family q).outcome b) *
              (evaluatedSliceFirstFactor params family q).total) *
          rightTensor (ι₁ := ι)
            (((evaluatedSlicePointMeas params strategy q.1).outcome a) *
              ((evaluatedSlicePointMeas params strategy q.2).outcome b))) -
      ev strategy.state
        (leftTensor (ι₂ := ι)
            (((evaluatedSliceFirstFactor params family q).outcome a) *
              ((evaluatedSliceSecondFactor params family q).outcome b)) *
          rightTensor (ι₁ := ι)
            (((evaluatedSlicePointMeas params strategy q.1).outcome a) *
              ((evaluatedSlicePointMeas params strategy q.2).outcome b))) =
    - ev strategy.state
        (leftTensor (ι₂ := ι)
            (((evaluatedSliceFirstFactor params family q).outcome a) *
              ((evaluatedSliceSecondFactor params family q).outcome b) *
              (1 - (G (pointHeight params q.1)).total)) *
          rightTensor (ι₁ := ι)
            (((evaluatedSlicePointMeas params strategy q.1).outcome a) *
              ((evaluatedSlicePointMeas params strategy q.2).outcome b))) := by
  have htotal : (evaluatedSliceFirstFactor params family q).total =
      (G (pointHeight params q.1)).total := by
    simpa [evaluatedSliceFirstFactor] using
      evaluatedPointFamily_total_eq_G_total params family G hG q.1
  let S : MIPStarRE.Quantum.Op ι :=
    ((evaluatedSliceFirstFactor params family q).outcome a) *
      ((evaluatedSliceSecondFactor params family q).outcome b)
  let T : MIPStarRE.Quantum.Op ι := (G (pointHeight params q.1)).total
  let P : MIPStarRE.Quantum.Op ι :=
    ((evaluatedSlicePointMeas params strategy q.1).outcome a) *
      ((evaluatedSlicePointMeas params strategy q.2).outcome b)
  change
    ev strategy.state
        (leftTensor (ι₂ := ι)
          (S * (evaluatedSliceFirstFactor params family q).total) *
        rightTensor (ι₁ := ι) P) -
      ev strategy.state (leftTensor (ι₂ := ι) S * rightTensor (ι₁ := ι) P) =
    - ev strategy.state (leftTensor (ι₂ := ι) (S * (1 - T)) * rightTensor (ι₁ := ι) P)
  rw [htotal]
  rw [← ev_sub]
  have hop :
      leftTensor (ι₂ := ι) (S * T) * rightTensor (ι₁ := ι) P -
          leftTensor (ι₂ := ι) S * rightTensor (ι₁ := ι) P =
        -(leftTensor (ι₂ := ι) (S * (1 - T)) * rightTensor (ι₁ := ι) P) := by
    calc
      leftTensor (ι₂ := ι) (S * T) * rightTensor (ι₁ := ι) P -
          leftTensor (ι₂ := ι) S * rightTensor (ι₁ := ι) P
        = opTensor (S * T) P - opTensor S P := by
            rw [leftTensor_mul_rightTensor_eq_opTensor,
              leftTensor_mul_rightTensor_eq_opTensor]
      _ = opTensor (S * T - S) P := by
            rw [MIPStarRE.LDT.opTensor_sub_left]
      _ = opTensor (-(S * (1 - T))) P := by
            have hs : S * T - S = -(S * (1 - T)) := by noncomm_ring
            rw [hs]
      _ = -(leftTensor (ι₂ := ι) (S * (1 - T)) * rightTensor (ι₁ := ι) P) := by
            have hneg : opTensor (-(S * (1 - T))) P = -(opTensor (S * (1 - T)) P) := by
              simpa [opTensor] using
                (Matrix.smul_kronecker (-1 : ℂ) (S * (1 - T)) P)
            rw [hneg]
            rw [leftTensor_mul_rightTensor_eq_opTensor]
  rw [hop]
  simpa using
    (ev_scale strategy.state (-1)
      (leftTensor (ι₂ := ι) (S * (1 - T)) * rightTensor (ι₁ := ι) P))









end MIPStarRE.LDT.Commutativity

end

end LIDT

open LIDT
/-!
# Phase-five endpoint for the evaluated-slice paper chain

This file isolates the paper line-87 removal endpoint and the finite
reindexing to the raw scalar `G`-commutativity stability defect.
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Paper-faithful phase-five removal after the right-register swap -/

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters) [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (strategy : _root_.LIDT.MIPStarRE.LDT.SymStrat params.next ι)
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    (G : _root_.LIDT.MIPStarRE.LDT.Fq params → _root_.LIDT.MIPStarRE.LDT.SubMeas (_root_.LIDT.MIPStarRE.LDT.Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas) :
    let 𝒟 := _root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params)
    let inserted : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Error := fun q =>
      ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params, ∑ b : _root_.LIDT.MIPStarRE.LDT.Fq params,
        _root_.LIDT.MIPStarRE.LDT.ev strategy.state
          (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
              (((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a) *
                ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceSecondFactor params family q).outcome b) *
                (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).total) *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
              (((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.1).outcome a) *
                ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.2).outcome b)))
    let removed : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Error :=
      _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseFivePaperRemoved params strategy family
    _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 inserted - _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 removed =
      -_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseFivePaperOrderedDefect params strategy family G) := by
  dsimp
  calc
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
        (fun q : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params =>
          ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params, ∑ b : _root_.LIDT.MIPStarRE.LDT.Fq params,
            _root_.LIDT.MIPStarRE.LDT.ev strategy.state
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                  (((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a) *
                    ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceSecondFactor params family q).outcome b) *
                    (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).total) *
                _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
                  (((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.1).outcome a) *
                    ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.2).outcome b)))) -
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
        (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseFivePaperRemoved params strategy family)
        = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
            (fun q : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params =>
              (∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params, ∑ b : _root_.LIDT.MIPStarRE.LDT.Fq params,
                _root_.LIDT.MIPStarRE.LDT.ev strategy.state
                  (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                      (((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a) *
                        ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceSecondFactor params family q).outcome b) *
                        (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).total) *
                    _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
                      (((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.1).outcome a) *
                        ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.2).outcome b)))) -
              _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseFivePaperRemoved params strategy family q) := by
            simp [_root_.LIDT.MIPStarRE.LDT.avgOver, Finset.sum_sub_distrib, mul_sub]
    _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
          (fun q => -_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseFivePaperOrderedDefect params strategy family G q) := by
            apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
            intro q
            calc
              (∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params, ∑ b : _root_.LIDT.MIPStarRE.LDT.Fq params,
                _root_.LIDT.MIPStarRE.LDT.ev strategy.state
                  (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                      (((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a) *
                        ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceSecondFactor params family q).outcome b) *
                        (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).total) *
                    _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
                      (((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.1).outcome a) *
                        ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.2).outcome b)))) -
                _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseFivePaperRemoved params strategy family q
                = ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params, ∑ b : _root_.LIDT.MIPStarRE.LDT.Fq params,
                    (_root_.LIDT.MIPStarRE.LDT.ev strategy.state
                      (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                          (((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a) *
                            ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceSecondFactor params family q).outcome b) *
                            (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).total) *
                        _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
                          (((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.1).outcome a) *
                            ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.2).outcome b))) -
                    _root_.LIDT.MIPStarRE.LDT.ev strategy.state
                      (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                          (((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a) *
                            ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceSecondFactor params family q).outcome b)) *
                        _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
                          (((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.1).outcome a) *
                            ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.2).outcome b)))) := by
                    simp [_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseFivePaperRemoved, Finset.sum_sub_distrib]
              _ = ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params, ∑ b : _root_.LIDT.MIPStarRE.LDT.Fq params,
                    -_root_.LIDT.MIPStarRE.LDT.ev strategy.state
                      (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                          (((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a) *
                            ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceSecondFactor params family q).outcome b) *
                            (1 - (G (_root_.LIDT.MIPStarRE.LDT.pointHeight params q.1)).total)) *
                        _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
                          (((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.1).outcome a) *
                            ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.2).outcome b))) := by
                    refine Finset.sum_congr rfl ?_
                    intro a _
                    refine Finset.sum_congr rfl ?_
                    intro b _
                    exact evaluatedSlice_phaseFivePaper_term_diff params strategy family G hG q a b
              _ = -_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseFivePaperOrderedDefect params strategy family G q := by
                    simp [_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseFivePaperOrderedDefect]
    _ = -_root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
          (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseFivePaperOrderedDefect params strategy family G) := by
            simp [_root_.LIDT.MIPStarRE.LDT.avgOver]
