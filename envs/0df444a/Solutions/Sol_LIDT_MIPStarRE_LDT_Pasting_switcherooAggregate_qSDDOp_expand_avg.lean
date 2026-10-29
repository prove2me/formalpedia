-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.switcherooAggregate_qSDDOp_expand_avg
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:03:35.789582+00:00
-- url     : https://prove2.me/submissions/3e5f4c68-33e5-46eb-b982-27cf31c83603

-- Generated proof for MIPStarRE.LDT.Pasting.switcherooAggregate_qSDDOp_expand_avg.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooContraction_ScalarTerms
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooContraction_Split
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooSetup_Centers
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooSetup_Terms
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_switcherooAggregate_qSDDOp_expand

namespace LIDT.MIPStarRE.LDT.Pasting
end LIDT.MIPStarRE.LDT.Pasting
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

namespace LIDT

end LIDT

open LIDT
/-!
# Section 12 pasting: switcheroo expansion

Expansion identities and the left-front contraction bound.
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem solution
    {Outcome : Type*} [Fintype Outcome]
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters) [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (ψbi : _root_.LIDT.MIPStarRE.LDT.QuantumState (ι × ι))
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    (M : _root_.LIDT.MIPStarRE.LDT.IdxProjSubMeas (_root_.LIDT.MIPStarRE.LDT.Fq params) Outcome ι) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params))
        (fun q => _root_.LIDT.MIPStarRE.LDT.qSDDOp ψbi
          (_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateLeft params family M q)
          (_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateRight params family M q)) =
      _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFirstTerm params ψbi family M +
        _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateSecondTerm params ψbi family M -
        _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateThirdTerm params ψbi family M -
        _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFourthTerm params ψbi family M := by
  let 𝒟q : _root_.LIDT.MIPStarRE.LDT.Distribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params) :=
    _root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params)
  let A : _root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params → _root_.LIDT.MIPStarRE.LDT.Error := fun q =>
    ∑ o : Outcome,
      _root_.LIDT.MIPStarRE.LDT.ev ψbi
        (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
          ((M q.2).outcome o *
            (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total *
            (M q.2).outcome o))
  let B : _root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params → _root_.LIDT.MIPStarRE.LDT.Error := fun q =>
    ∑ o : Outcome,
      _root_.LIDT.MIPStarRE.LDT.ev ψbi
        (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
          ((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total *
            (M q.2).outcome o *
            (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total))
  let C : _root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params → _root_.LIDT.MIPStarRE.LDT.Error := fun q =>
    ∑ o : Outcome,
      _root_.LIDT.MIPStarRE.LDT.ev ψbi
        (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
          ((M q.2).outcome o *
            (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total *
            (M q.2).outcome o *
            (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total))
  let D : _root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params → _root_.LIDT.MIPStarRE.LDT.Error := fun q =>
    ∑ o : Outcome,
      _root_.LIDT.MIPStarRE.LDT.ev ψbi
        (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
          ((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total *
            (M q.2).outcome o *
            (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total *
            (M q.2).outcome o))
  have hA :
      _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟q A = _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFirstTerm params ψbi family M := by
    rfl
  have hB :
      _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟q B = _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateSecondTerm params ψbi family M := by
    rfl
  have hC :
      _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟q C = _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateThirdTerm params ψbi family M := by
    rfl
  have hD :
      _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟q D = _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFourthTerm params ψbi family M := by
    rfl
  change _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟q
      (fun q => _root_.LIDT.MIPStarRE.LDT.qSDDOp ψbi
        (_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateLeft params family M q)
        (_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateRight params family M q)) = _
  calc
    _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟q
        (fun q => _root_.LIDT.MIPStarRE.LDT.qSDDOp ψbi
          (_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateLeft params family M q)
          (_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateRight params family M q))
      = _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟q (fun q => A q + B q - C q - D q) := by
          apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
          intro q
          rw [_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregate_qSDDOp_expand]
          simp [A, B, C, D, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟q A + _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟q B - _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟q C - _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟q D := by
          rw [show (fun q => A q + B q - C q - D q) =
              fun q => (A q + B q) + ((-1 : _root_.LIDT.MIPStarRE.LDT.Error) * C q + (-1 : _root_.LIDT.MIPStarRE.LDT.Error) * D q) by
                funext q
                ring]
          rw [_root_.LIDT.MIPStarRE.LDT.avgOver_add, _root_.LIDT.MIPStarRE.LDT.avgOver_add, _root_.LIDT.MIPStarRE.LDT.avgOver_add, _root_.LIDT.MIPStarRE.LDT.avgOver_const_mul, _root_.LIDT.MIPStarRE.LDT.avgOver_const_mul]
          simp [sub_eq_add_neg]
          ring
    _ = _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFirstTerm params ψbi family M +
          _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateSecondTerm params ψbi family M -
          _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateThirdTerm params ψbi family M -
          _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFourthTerm params ψbi family M := by
          rw [hA, hB, hC, hD]
