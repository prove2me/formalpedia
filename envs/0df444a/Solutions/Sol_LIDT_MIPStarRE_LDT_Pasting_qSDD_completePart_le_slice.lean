-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.qSDD_completePart_le_slice
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T16:40:01.311537+00:00
-- url     : https://prove2.me/submissions/4ced3e07-93c7-47fa-9b20-ede212e517fc

-- Generated proof for MIPStarRE.LDT.Pasting.qSDD_completePart_le_slice.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomialEmbedding
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Tuples
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_GHatSandwich
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_PastedFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_Switcheroo
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Local
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

open scoped _root_.Matrix

namespace LIDT.MIPStarRE.LDT.Pasting
end LIDT.MIPStarRE.LDT.Pasting
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

namespace LIDT

end LIDT

open LIDT
/-!
# Section 12 pasting: complete and incomplete part self-consistency

Scalar and state-dependent-distance consequences for the complete and incomplete
parts of the pasted slice family.
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters)
    [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (ψbi : _root_.LIDT.MIPStarRE.LDT.QuantumState (ι × ι))
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    (x : _root_.LIDT.MIPStarRE.LDT.Fq params) :
    _root_.LIDT.MIPStarRE.LDT.qSDD ψbi
        ((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family x).liftLeft)
        ((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family x).liftRight)
      ≤
    _root_.LIDT.MIPStarRE.LDT.qSDD ψbi
        (((family.meas x).toSubMeas).liftLeft)
        (((family.meas x).toSubMeas).liftRight) := by
  let P := family.meas x
  let T : _root_.LIDT.MIPStarRE.Quantum.Op ι := P.total
  have hTT : T * T = T := by
    simpa [T, P] using _root_.LIDT.MIPStarRE.LDT.Preliminaries.projSubMeas_total_proj P
  have hcomplete :
      _root_.LIDT.MIPStarRE.LDT.qSDD ψbi ((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family x).liftLeft)
          ((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family x).liftRight) =
        _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T) +
          _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) T) -
          2 * _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.opTensor T T) := by
    calc
      _root_.LIDT.MIPStarRE.LDT.qSDD ψbi ((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family x).liftLeft)
          ((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family x).liftRight)
        = _root_.LIDT.MIPStarRE.LDT.ev ψbi (((_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T - _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) T)ᴴ) *
            (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T - _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) T)) := by
              unfold _root_.LIDT.MIPStarRE.LDT.qSDD _root_.LIDT.MIPStarRE.LDT.qSDDCore
              simp only [Finset.univ_unique, PUnit.default_eq_unit,
                _root_.LIDT.MIPStarRE.LDT.SubMeas.liftLeft, _root_.LIDT.MIPStarRE.LDT.SubMeas.liftRight,
                _root_.LIDT.MIPStarRE.LDT.mkLeftPlacedSubMeas_outcome, _root_.LIDT.MIPStarRE.LDT.mkRightPlacedSubMeas_outcome,
                Matrix.conjTranspose_sub, Finset.sum_singleton,
                _root_.LIDT.MIPStarRE.LDT.leftTensor_conjTranspose, _root_.LIDT.MIPStarRE.LDT.rightTensor_conjTranspose,
                _root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas_outcome_unit, _root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas_total, T]
              simp [P]
      _ = _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (T * T)) +
            _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (T * T)) - 2 * _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.opTensor T T) := by
              have hLherm : (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T)ᴴ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T := by
                exact
                  (Matrix.nonneg_iff_posSemidef.mp
                    (_root_.LIDT.MIPStarRE.LDT.leftTensor_nonneg (ι₂ := ι)
                      (_root_.LIDT.MIPStarRE.LDT.SubMeas.total_nonneg P.toSubMeas))).isHermitian.eq
              have hRherm : (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) T)ᴴ = _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) T := by
                exact
                  (Matrix.nonneg_iff_posSemidef.mp
                    (_root_.LIDT.MIPStarRE.LDT.rightTensor_nonneg (ι₁ := ι)
                    (_root_.LIDT.MIPStarRE.LDT.SubMeas.total_nonneg P.toSubMeas))).isHermitian.eq
              calc
                _root_.LIDT.MIPStarRE.LDT.ev ψbi (((_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T - _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) T)ᴴ) *
                    (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T - _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) T))
                  = _root_.LIDT.MIPStarRE.LDT.ev ψbi (((_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T * _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T -
                        _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) T) -
                      (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) T * _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T -
                        _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) T * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) T))) := by
                          congr 1
                          simp [hLherm, hRherm, sub_mul, mul_sub]
                          abel
                _ = _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (T * T)) +
                      _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (T * T)) - 2 * _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.opTensor T T) := by
                          rw [_root_.LIDT.MIPStarRE.LDT.ev_sub, _root_.LIDT.MIPStarRE.LDT.ev_sub, _root_.LIDT.MIPStarRE.LDT.ev_sub]
                          rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_mul_leftTensor,
                            _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor,
                            _root_.LIDT.MIPStarRE.LDT.rightTensor_mul_leftTensor_eq_opTensor,
                            _root_.LIDT.MIPStarRE.LDT.rightTensor_mul_rightTensor]
                          ring
      _ = _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T) +
            _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) T) -
            2 * _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.opTensor T T) := by
            simp [hTT]
  have horig :
      _root_.LIDT.MIPStarRE.LDT.qSDD ψbi (((family.meas x).toSubMeas).liftLeft)
          (((family.meas x).toSubMeas).liftRight) =
        _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T) +
          _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) T) -
          2 * ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.opTensor (P.outcome g) (P.outcome g)) := by
    have hsum_left :
        ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (P.outcome g)) =
          _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T) := by
      calc
        ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (P.outcome g))
          = _root_.LIDT.MIPStarRE.LDT.ev ψbi (∑ a, _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (P.outcome a)) := by
              rw [← _root_.LIDT.MIPStarRE.LDT.ev_sum ψbi (fun g => _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (P.outcome g))]
        _ = _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (∑ a, P.outcome a)) := by
              rw [← _root_.LIDT.MIPStarRE.LDT.leftTensor_finset_sum (ι₂ := ι) Finset.univ P.outcome]
        _ = _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T) := by simp [T, P.sum_eq_total]
    have hsum_right :
        ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (P.outcome g)) =
          _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) T) := by
      calc
        ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (P.outcome g))
          = _root_.LIDT.MIPStarRE.LDT.ev ψbi (∑ a, _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (P.outcome a)) := by
              rw [← _root_.LIDT.MIPStarRE.LDT.ev_sum ψbi (fun g => _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (P.outcome g))]
        _ = _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (∑ a, P.outcome a)) := by
              rw [← _root_.LIDT.MIPStarRE.LDT.rightTensor_finset_sum (ι₁ := ι) Finset.univ P.outcome]
        _ = _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) T) := by simp [T, P.sum_eq_total]
    unfold _root_.LIDT.MIPStarRE.LDT.qSDD _root_.LIDT.MIPStarRE.LDT.qSDDCore
    calc
      ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params,
          _root_.LIDT.MIPStarRE.LDT.ev ψbi
            ((((P.toSubMeas.liftLeft).outcome g - (P.toSubMeas.liftRight).outcome g)ᴴ) *
              ((P.toSubMeas.liftLeft).outcome g - (P.toSubMeas.liftRight).outcome g))
        = ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params,
            (_root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (P.outcome g)) +
              _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (P.outcome g)) -
              2 * _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.opTensor (P.outcome g) (P.outcome g))) := by
              refine Finset.sum_congr rfl ?_
              intro g _
              have hLherm :
                  (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (P.outcome g))ᴴ =
                    _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (P.outcome g) := by
                exact
                  (Matrix.nonneg_iff_posSemidef.mp
                    (_root_.LIDT.MIPStarRE.LDT.leftTensor_nonneg (ι₂ := ι) (P.outcome_pos g))).isHermitian.eq
              have hRherm :
                  (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (P.outcome g))ᴴ =
                    _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (P.outcome g) := by
                exact
                  (Matrix.nonneg_iff_posSemidef.mp
                    (_root_.LIDT.MIPStarRE.LDT.rightTensor_nonneg (ι₁ := ι) (P.outcome_pos g))).isHermitian.eq
              calc
                _root_.LIDT.MIPStarRE.LDT.ev ψbi
                    ((((P.toSubMeas.liftLeft).outcome g - (P.toSubMeas.liftRight).outcome g)ᴴ) *
                      ((P.toSubMeas.liftLeft).outcome g - (P.toSubMeas.liftRight).outcome g))
                  = _root_.LIDT.MIPStarRE.LDT.ev ψbi
                      (((_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (P.outcome g) *
                            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (P.outcome g) -
                          _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (P.outcome g) *
                            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (P.outcome g)) -
                        (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (P.outcome g) *
                            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (P.outcome g) -
                          _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (P.outcome g) *
                            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (P.outcome g)))) := by
                          congr 1
                          simp [_root_.LIDT.MIPStarRE.LDT.SubMeas.liftLeft, _root_.LIDT.MIPStarRE.LDT.SubMeas.liftRight, hLherm, hRherm,
                            sub_mul, mul_sub]
                          abel
                _ = _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (P.outcome g * P.outcome g)) +
                      _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (P.outcome g * P.outcome g)) -
                      2 * _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.opTensor (P.outcome g) (P.outcome g)) := by
                          rw [_root_.LIDT.MIPStarRE.LDT.ev_sub, _root_.LIDT.MIPStarRE.LDT.ev_sub, _root_.LIDT.MIPStarRE.LDT.ev_sub]
                          rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_mul_leftTensor,
                            _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor,
                            _root_.LIDT.MIPStarRE.LDT.rightTensor_mul_leftTensor_eq_opTensor,
                            _root_.LIDT.MIPStarRE.LDT.rightTensor_mul_rightTensor]
                          ring
                _ = _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (P.outcome g)) +
                      _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (P.outcome g)) -
                      2 * _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.opTensor (P.outcome g) (P.outcome g)) := by
                          simp [P.proj g]
      _ = (∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params,
              (_root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (P.outcome g)) +
                _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (P.outcome g)))) -
            ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, 2 * _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.opTensor (P.outcome g) (P.outcome g)) := by
              rw [Finset.sum_sub_distrib]
      _ = (∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (P.outcome g))) +
            ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (P.outcome g)) -
            ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, 2 * _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.opTensor (P.outcome g) (P.outcome g)) := by
              rw [Finset.sum_add_distrib]
      _ = _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T) + _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) T) -
            ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, 2 * _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.opTensor (P.outcome g) (P.outcome g)) := by
              rw [hsum_left, hsum_right]
      _ = _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T) + _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) T) -
            2 * ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.opTensor (P.outcome g) (P.outcome g)) := by
              rw [← Finset.mul_sum]
  have hmatch :
      ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.opTensor (P.outcome g) (P.outcome g)) ≤
        _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.opTensor T T) := by
    simpa [T, P, _root_.LIDT.MIPStarRE.LDT.qMatchMass, _root_.LIDT.MIPStarRE.LDT.leftPlacedSubMeas, _root_.LIDT.MIPStarRE.LDT.rightPlacedSubMeas, _root_.LIDT.MIPStarRE.LDT.postprocess,
      _root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas, _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor, P.sum_eq_total] using
      _root_.LIDT.MIPStarRE.LDT.Preliminaries.qMatchMass_leftRight_postprocess_ge
        ψbi P.toSubMeas P.toSubMeas (fun _ => ())
  rw [hcomplete, horig]
  nlinarith
