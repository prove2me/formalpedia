-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.switcherooAggregate_qSDDOp_expand
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T16:59:18.085761+00:00
-- url     : https://prove2.me/submissions/73a35d70-8c14-4003-98b5-02ceb413cba5

-- Generated proof for MIPStarRE.LDT.Pasting.switcherooAggregate_qSDDOp_expand.
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

/- Source helpers from MIPStarRE/LDT/Pasting/SwitcherooSetup/Infrastructure.lean. -/
/-!
# Section 12 pasting: switcheroo infrastructure

Initial switcheroo infrastructure and aggregate expansion helpers.
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Switcheroo infrastructure -/











/-- The total operator of a projective submeasurement is idempotent. -/
lemma projSubMeas_total_sq
    {Outcome : Type*} [Fintype Outcome]
    (P : ProjSubMeas Outcome ι) :
    P.toSubMeas.total * P.toSubMeas.total = P.toSubMeas.total := by
  simpa using MIPStarRE.LDT.Preliminaries.projSubMeas_total_proj P



end MIPStarRE.LDT.Pasting

end

end LIDT

open LIDT
/-!
# Section 12 pasting: switcheroo infrastructure

Initial switcheroo infrastructure and aggregate expansion helpers.
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Switcheroo infrastructure -/

theorem solution
    {Outcome : Type*} [Fintype Outcome]
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters) [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (ψbi : _root_.LIDT.MIPStarRE.LDT.QuantumState (ι × ι))
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    (M : _root_.LIDT.MIPStarRE.LDT.IdxProjSubMeas (_root_.LIDT.MIPStarRE.LDT.Fq params) Outcome ι)
    (q : _root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params) :
    _root_.LIDT.MIPStarRE.LDT.qSDDOp ψbi
      (_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateLeft params family M q)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateRight params family M q)
      =
        ∑ o : Outcome,
          (_root_.LIDT.MIPStarRE.LDT.ev ψbi
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                ((M q.2).outcome o *
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total *
                  (M q.2).outcome o)) +
            _root_.LIDT.MIPStarRE.LDT.ev ψbi
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                ((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total *
                  (M q.2).outcome o *
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total)) -
            _root_.LIDT.MIPStarRE.LDT.ev ψbi
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                ((M q.2).outcome o *
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total *
                  (M q.2).outcome o *
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total)) -
            _root_.LIDT.MIPStarRE.LDT.ev ψbi
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                ((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total *
                  (M q.2).outcome o *
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total *
                  (M q.2).outcome o))) := by
  let G : _root_.LIDT.MIPStarRE.Quantum.Op ι := (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total
  have hGsq : G * G = G := by
    simpa [G, _root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas, _root_.LIDT.MIPStarRE.LDT.postprocess_total] using
      _root_.LIDT.MIPStarRE.LDT.Pasting.projSubMeas_total_sq (family.meas q.1)
  unfold _root_.LIDT.MIPStarRE.LDT.qSDDOp _root_.LIDT.MIPStarRE.LDT.qSDDCore
  refine Finset.sum_congr rfl ?_
  intro o _
  let Mo : _root_.LIDT.MIPStarRE.Quantum.Op ι := (M q.2).outcome o
  have hMosq : Mo * Mo = Mo := by
    simpa [Mo] using (M q.2).proj o
  have hGherm : (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) G)ᴴ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) G := by
    exact
      (Matrix.nonneg_iff_posSemidef.mp
        (_root_.LIDT.MIPStarRE.LDT.leftTensor_nonneg (ι₂ := ι)
          (_root_.LIDT.MIPStarRE.LDT.SubMeas.total_nonneg (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1)))).isHermitian.eq
  have hMoherm : (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) Mo)ᴴ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) Mo := by
    exact
      (Matrix.nonneg_iff_posSemidef.mp
        (_root_.LIDT.MIPStarRE.LDT.leftTensor_nonneg (ι₂ := ι) ((M q.2).outcome_pos o))).isHermitian.eq
  calc
    _root_.LIDT.MIPStarRE.LDT.ev ψbi
        ((((_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateLeft params family M q).outcome o -
              (_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateRight params family M q).outcome o)ᴴ) *
          ((_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateLeft params family M q).outcome o -
            (_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateRight params family M q).outcome o))
      = _root_.LIDT.MIPStarRE.LDT.ev ψbi
          ((((_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) G * _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) Mo) -
                (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) Mo * _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) G))ᴴ) *
            ((_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) G * _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) Mo) -
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) Mo * _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) G))) := by
            simp [_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateLeft, _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateRight,
              _root_.LIDT.MIPStarRE.LDT.Pasting.multiplyByTotalOnLeft, _root_.LIDT.MIPStarRE.LDT.Pasting.multiplyByTotalOnRight,
              _root_.LIDT.MIPStarRE.LDT.OpFamily.leftPlacedOpFamily, _root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas, G, Mo,
              _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_leftTensor, _root_.LIDT.MIPStarRE.LDT.postprocess_total]
    _ = _root_.LIDT.MIPStarRE.LDT.ev ψbi
          (((_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) Mo * _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) G) -
                (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) G * _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) Mo)) *
            ((_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) G * _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) Mo) -
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) Mo * _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) G))) := by
            simp [hGherm, hMoherm]
    _ = _root_.LIDT.MIPStarRE.LDT.ev ψbi
          ((_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) Mo * _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) G *
                _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) G * _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) Mo) +
            (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) G * _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) Mo *
                _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) Mo * _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) G) -
            (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) Mo * _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) G *
                _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) Mo * _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) G) -
            (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) G * _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) Mo *
                _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) G * _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) Mo)) := by
            congr 1
            noncomm_ring
    _ = _root_.LIDT.MIPStarRE.LDT.ev ψbi
          (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (Mo * G * Mo) +
            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (G * Mo * G) -
            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (Mo * G * Mo * G) -
            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (G * Mo * G * Mo)) := by
            simp [_root_.LIDT.MIPStarRE.LDT.leftTensor_mul_leftTensor, hGsq, hMosq, mul_assoc]
    _ =
        _root_.LIDT.MIPStarRE.LDT.ev ψbi
          (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (Mo * G * Mo)) +
        _root_.LIDT.MIPStarRE.LDT.ev ψbi
          (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (G * Mo * G)) -
        _root_.LIDT.MIPStarRE.LDT.ev ψbi
          (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (Mo * G * Mo * G)) -
        _root_.LIDT.MIPStarRE.LDT.ev ψbi
          (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (G * Mo * G * Mo)) := by
            rw [_root_.LIDT.MIPStarRE.LDT.ev_sub, _root_.LIDT.MIPStarRE.LDT.ev_sub, _root_.LIDT.MIPStarRE.LDT.ev_add]
    _ =
        _root_.LIDT.MIPStarRE.LDT.ev ψbi
            (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
              ((M q.2).outcome o * (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total *
                (M q.2).outcome o)) +
          _root_.LIDT.MIPStarRE.LDT.ev ψbi
            (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
              ((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total * (M q.2).outcome o *
                (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total)) -
          _root_.LIDT.MIPStarRE.LDT.ev ψbi
            (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
              ((M q.2).outcome o * (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total *
                (M q.2).outcome o * (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total)) -
          _root_.LIDT.MIPStarRE.LDT.ev ψbi
            (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
              ((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total * (M q.2).outcome o *
                (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total * (M q.2).outcome o)) := by
            simp [G, Mo]
