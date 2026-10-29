-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.commutativitySwitcheroo_ofCompleteSelfConsistency
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:40:46.308845+00:00
-- url     : https://prove2.me/submissions/9b89b01c-764d-47bf-be79-efcf484c9682

-- Generated proof for MIPStarRE.LDT.Pasting.commutativitySwitcheroo_ofCompleteSelfConsistency.
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_switcherooAggregateFirstTerm_eq_leftSandwich
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_switcherooAggregateFirstTerm_eq_split_by_g
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_switcherooAggregateFourthTerm_split_close_once_commuted
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_switcherooAggregateLeftFrontScalar_close_firstSplitScalar
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_switcherooAggregateMGCenterComplete_eq_opTensor_avg
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_switcherooAggregateMixedScalar_close_leftFrontScalar
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_switcherooAggregateOnceCommutedScalar_close_mixed
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_switcherooAggregateTarget_eq_middleSandwich
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_switcherooAggregateTarget_eq_opTensor_avg
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_switcherooAggregateThirdTerm_eq_fourthTerm
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_switcherooAggregate_qSDDOp_expand_avg
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_switcheroo_first_term_close
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_switcheroo_second_aggregate_term_close

namespace LIDT.MIPStarRE.LDT.CommutativityPoints
end LIDT.MIPStarRE.LDT.CommutativityPoints
namespace LIDT.MIPStarRE.LDT.Pasting
end LIDT.MIPStarRE.LDT.Pasting
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

namespace LIDT

/- Source helpers from MIPStarRE/LDT/Pasting/SwitcherooCompletion.lean. -/
/-!
# Section 12 pasting: switcheroo completion bounds

Completion and first-stage switcheroo error bounds.
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma switcherooCompletePartCenter_eq_target
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (hfix : swapDensity ψbi.density = ψbi.density)
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) :
    avgOver (uniformDistribution (SliceQuestion params)) (fun y =>
      Preliminaries.middleSandwichExpectation ψbi
        (uniformDistribution (SliceQuestion params))
        (completePartProjFamily params family) (((M y).toSubMeas).total)) =
      switcherooAggregateTarget params ψbi family M := by
  calc
    avgOver (uniformDistribution (SliceQuestion params)) (fun y =>
        Preliminaries.middleSandwichExpectation ψbi
          (uniformDistribution (SliceQuestion params))
          (completePartProjFamily params family) (((M y).toSubMeas).total))
      = avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
          ev ψbi
            (opTensor
              (((M q.2).toSubMeas).total)
              ((completePartSubMeas params family q.1).total))) := by
          simpa using
            switcherooAggregateMGCenterComplete_eq_opTensor_avg
              (ι := ι) (params := params) (ψbi := ψbi) (family := family) (M := M)
    _ = avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
          ev ψbi
            (opTensor
              ((completePartSubMeas params family q.1).total)
              (((M q.2).toSubMeas).total))) := by
          apply avgOver_congr
          intro q
          simpa using
            (ev_opTensor_swap_of_density_fixed ψbi hfix
              (((M q.2).toSubMeas).total)
              ((completePartSubMeas params family q.1).total))
    _ = switcherooAggregateTarget params ψbi family M := by
          simpa using
            (switcherooAggregateTarget_eq_opTensor_avg
              (ι := ι) (params := params) (ψbi := ψbi) (family := family) (M := M)).symm

-- After extracting the pointwise normalization helpers above, the final
-- four-term assembly proof elaborates within the default heartbeat budget.




end MIPStarRE.LDT.Pasting

end

/- Source helpers from MIPStarRE/LDT/Pasting/SwitcherooContraction/ScalarTerms.lean. -/
/-!
# Section 12 pasting: switcheroo scalar expressions

Named scalar expressions for the switcheroo contraction chain.
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]







/-- Restate the first `sqrt chi` step using the named scalar expression. -/
lemma switcherooAggregateFourthTerm_close_once_commuted_scalar
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (hnorm : ψbi.IsNormalized)
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι)
    (chi : Error)
    (hcomm : SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (switcherooPointProductLeft params family M)
      (switcherooPointProductRight params family M)
      chi) :
    |switcherooAggregateFourthTerm params ψbi family M -
        switcherooAggregateOnceCommutedScalar params ψbi family M| ≤
      Real.sqrt chi := by
  simpa [switcherooAggregateOnceCommutedScalar] using
    switcherooAggregateFourthTerm_split_close_once_commuted
      params ψbi hnorm family M chi hcomm





end MIPStarRE.LDT.Pasting

end

end LIDT

open LIDT
/-!
# Section 12 pasting: switcheroo completion bounds

Completion and first-stage switcheroo error bounds.
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]



-- After extracting the pointwise normalization helpers above, the final
-- four-term assembly proof elaborates within the default heartbeat budget.

theorem solution
    {Outcome : Type*} [Fintype Outcome]
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters) [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (ψbi : _root_.LIDT.MIPStarRE.LDT.QuantumState (ι × ι))
    (hnorm : ψbi.IsNormalized)
    (hfix : _root_.LIDT.MIPStarRE.LDT.swapDensity ψbi.density = ψbi.density)
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    (M : _root_.LIDT.MIPStarRE.LDT.IdxProjSubMeas (_root_.LIDT.MIPStarRE.LDT.Fq params) Outcome ι)
    (zeta omega chi : _root_.LIDT.MIPStarRE.LDT.Error)
    (hselfG : _root_.LIDT.MIPStarRE.LDT.Pasting.GCompleteSelfConsistencyStatement params ψbi family zeta)
    (hselfM : _root_.LIDT.MIPStarRE.LDT.SDDRel ψbi
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params))
      (_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooSelfConsistencyLeft params M)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooSelfConsistencyRight params M)
      omega)
    (hcomm : _root_.LIDT.MIPStarRE.LDT.SDDOpRel ψbi
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params))
      (_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooPointProductLeft params family M)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooPointProductRight params family M)
      chi) :
    _root_.LIDT.MIPStarRE.LDT.Pasting.CommutativitySwitcherooStatement params ψbi family M zeta omega chi := by
  /-
  Paper reference: `lem:commutativity-switcheroo` in
  `references/ldt-paper/ld-pasting.tex`.
  This is the main aggregate-commutation step upgrading commutation with each
  `G^x_g` to commutation with the total `G^x`.

  The paper informally compares all four `qSDDOp` expansion terms to a single
  scalar center. In Lean it is cleaner to use two centers whose contributions
  cancel algebraically:

  * `G ⊗ M` for the first/third terms
  * `M ⊗ G` for the second/fourth terms

  This avoids inserting an extra symmetry assumption on `ψbi` at this stage.
  -/
  refine ⟨?_⟩
  let 𝒟x : _root_.LIDT.MIPStarRE.LDT.Distribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params) :=
    _root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params)
  let firstTerm :=
    _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟x (fun x =>
      _root_.LIDT.MIPStarRE.LDT.Preliminaries.leftSandwichExpectation ψbi 𝒟x M
        ((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family x).total))
  let secondTerm := _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateSecondTerm params ψbi family M
  let thirdTerm := _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateThirdTerm params ψbi family M
  let fourthTerm := _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFourthTerm params ψbi family M
  let centerGM := _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateTarget params ψbi family M
  let centerMGComplete : _root_.LIDT.MIPStarRE.LDT.Error :=
    _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟x (fun y =>
      _root_.LIDT.MIPStarRE.LDT.Preliminaries.middleSandwichExpectation ψbi 𝒟x
        (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartProjFamily params family) (((M y).toSubMeas).total))
  have hfirst : |firstTerm - centerGM| ≤ 2 * Real.sqrt omega := by
    simpa [firstTerm, centerGM, _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateTarget_eq_middleSandwich] using
      _root_.LIDT.MIPStarRE.LDT.Pasting.switcheroo_first_term_close params ψbi hnorm family M omega hselfM
  have hsecond : |secondTerm - centerMGComplete| ≤ 2 * Real.sqrt zeta := by
    simpa [secondTerm, centerMGComplete, 𝒟x] using
      _root_.LIDT.MIPStarRE.LDT.Pasting.switcheroo_second_aggregate_term_close params ψbi hnorm family M zeta hselfG
  have hexpand := _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregate_qSDDOp_expand_avg params ψbi family M
  have hthird_eq : thirdTerm = fourthTerm := by
    simpa [thirdTerm, fourthTerm] using
      _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateThirdTerm_eq_fourthTerm params ψbi family M
  have hcenter : centerMGComplete = centerGM := by
    simpa [centerGM, centerMGComplete] using
      switcherooCompletePartCenter_eq_target params ψbi hfix family M
  have hsecond' : |secondTerm - centerGM| ≤ 2 * Real.sqrt zeta := by
    simpa [hcenter] using hsecond
  have hfirst_eq :
      _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFirstTerm params ψbi family M = firstTerm := by
    simpa [firstTerm, _root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas, _root_.LIDT.MIPStarRE.LDT.postprocess_total] using
      _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFirstTerm_eq_leftSandwich params ψbi family M
  have hstep1 :=
    _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFourthTerm_close_once_commuted_scalar
      params ψbi hnorm family M chi hcomm
  have hstep2 :
      |_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateOnceCommutedScalar params ψbi family M -
          _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateMixedScalar params ψbi family M| ≤ Real.sqrt zeta := by
    exact _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateOnceCommutedScalar_close_mixed
      params ψbi hnorm family M zeta hselfG
  have hstep3 :
      |_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateMixedScalar params ψbi family M -
          _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateLeftFrontScalar params ψbi family M| ≤ Real.sqrt zeta := by
    exact _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateMixedScalar_close_leftFrontScalar
      params ψbi hnorm family M zeta hselfG
  have hstep4 :=
    _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateLeftFrontScalar_close_firstSplitScalar
      params ψbi hnorm family M chi hcomm
  have hstep5 :
      _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFirstSplitScalar params ψbi family M =
        _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFirstTerm params ψbi family M := by
    simpa [_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFirstSplitScalar, mul_assoc] using
      _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFirstTerm_eq_split_by_g params ψbi family M
  have hstep5' :
      |_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFirstSplitScalar params ψbi family M -
          _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFirstTerm params ψbi family M| ≤ 0 := by
    rw [hstep5]
    simp
  have hfourth_first :
      |_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFourthTerm params ψbi family M -
          _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFirstTerm params ψbi family M| ≤
        2 * Real.sqrt zeta + 2 * Real.sqrt chi := by
    calc
      |_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFourthTerm params ψbi family M -
          _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFirstTerm params ψbi family M|
        ≤ |_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFourthTerm params ψbi family M -
              _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateOnceCommutedScalar params ψbi family M| +
            |_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateOnceCommutedScalar params ψbi family M -
              _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateMixedScalar params ψbi family M| +
            |_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateMixedScalar params ψbi family M -
              _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateLeftFrontScalar params ψbi family M| +
            |_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateLeftFrontScalar params ψbi family M -
              _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFirstSplitScalar params ψbi family M| +
            |_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFirstSplitScalar params ψbi family M -
              _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFirstTerm params ψbi family M| := by
              nlinarith [abs_sub_le
                (_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFourthTerm params ψbi family M)
                (_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateOnceCommutedScalar params ψbi family M)
                (_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFirstTerm params ψbi family M),
                abs_sub_le
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateOnceCommutedScalar params ψbi family M)
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateMixedScalar params ψbi family M)
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFirstTerm params ψbi family M),
                abs_sub_le
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateMixedScalar params ψbi family M)
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateLeftFrontScalar params ψbi family M)
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFirstTerm params ψbi family M),
                abs_sub_le
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateLeftFrontScalar params ψbi family M)
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFirstSplitScalar params ψbi family M)
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFirstTerm params ψbi family M)]
      _ ≤ Real.sqrt chi + Real.sqrt zeta + Real.sqrt zeta + Real.sqrt chi + 0 := by
            nlinarith [hstep1, hstep2, hstep3, hstep4, hstep5']
      _ = 2 * Real.sqrt zeta + 2 * Real.sqrt chi := by ring
  have hfourth_first' :
      |fourthTerm - firstTerm| ≤ 2 * Real.sqrt zeta + 2 * Real.sqrt chi := by
    rw [← hfirst_eq]
    simpa [fourthTerm] using hfourth_first
  have hfourth : |fourthTerm - centerGM| ≤
      2 * Real.sqrt zeta + 2 * Real.sqrt chi + 2 * Real.sqrt omega := by
    calc
      |fourthTerm - centerGM| ≤ |fourthTerm - firstTerm| + |firstTerm - centerGM| := by
            simpa [add_comm, add_left_comm, add_assoc] using
              (abs_sub_le fourthTerm firstTerm centerGM)
      _ ≤ (2 * Real.sqrt zeta + 2 * Real.sqrt chi) + 2 * Real.sqrt omega := by
            exact add_le_add hfourth_first' hfirst
      _ = 2 * Real.sqrt zeta + 2 * Real.sqrt chi + 2 * Real.sqrt omega := by ring
  have hthird : |thirdTerm - centerGM| ≤
      2 * Real.sqrt zeta + 2 * Real.sqrt chi + 2 * Real.sqrt omega := by
    rw [hthird_eq]
    exact hfourth
  constructor
  unfold _root_.LIDT.MIPStarRE.LDT.sddErrorOp
  rw [hexpand]
  have hdecomp :
      firstTerm + secondTerm - thirdTerm - fourthTerm ≤
        |firstTerm - centerGM| + |secondTerm - centerGM| +
          |thirdTerm - centerGM| + |fourthTerm - centerGM| := by
    have hfirst_le : firstTerm - centerGM ≤ |firstTerm - centerGM| := by
      exact le_abs_self _
    have hsecond_le : secondTerm - centerGM ≤ |secondTerm - centerGM| := by
      exact le_abs_self _
    have hthird_le : -(thirdTerm - centerGM) ≤ |thirdTerm - centerGM| := by
      exact neg_le_abs _
    have hfourth_le : -(fourthTerm - centerGM) ≤ |fourthTerm - centerGM| := by
      exact neg_le_abs _
    have hrewrite :
        firstTerm + secondTerm - thirdTerm - fourthTerm =
          (firstTerm - centerGM) + (secondTerm - centerGM) -
            (thirdTerm - centerGM) - (fourthTerm - centerGM) := by
      ring
    rw [hrewrite]
    nlinarith
  have hmain_eq :
      _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFirstTerm params ψbi family M + secondTerm - thirdTerm - fourthTerm =
        firstTerm + secondTerm - thirdTerm - fourthTerm := by
    exact congrArg (fun t => t + secondTerm - thirdTerm - fourthTerm) hfirst_eq
  calc
    _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFirstTerm params ψbi family M +
        _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateSecondTerm params ψbi family M -
        _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateThirdTerm params ψbi family M -
        _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFourthTerm params ψbi family M
      = firstTerm + secondTerm - thirdTerm - fourthTerm := by
          simpa [secondTerm, thirdTerm, fourthTerm] using hmain_eq
    _
      ≤ |firstTerm - centerGM| + |secondTerm - centerGM| +
          |thirdTerm - centerGM| + |fourthTerm - centerGM| := hdecomp
    _ ≤ 2 * Real.sqrt omega + 2 * Real.sqrt zeta +
          (2 * Real.sqrt zeta + 2 * Real.sqrt chi + 2 * Real.sqrt omega) +
          (2 * Real.sqrt zeta + 2 * Real.sqrt chi + 2 * Real.sqrt omega) := by
            nlinarith [hfirst, hsecond', hthird, hfourth]
    _ = _root_.LIDT.MIPStarRE.LDT.Pasting.commutativitySwitcherooError zeta omega chi := by
          simp [_root_.LIDT.MIPStarRE.LDT.Pasting.commutativitySwitcherooError, Real.sqrt_eq_rpow]
          ring
