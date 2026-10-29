-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateMGCenterComplete_eq_opTensor_avg
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T16:51:31.699691+00:00
-- url     : https://prove2.me/submissions/34725292-0288-4c6f-91f0-5b1a454a2918

-- Generated proof for MIPStarRE.LDT.Pasting.switcherooAggregateMGCenterComplete_eq_opTensor_avg.
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

namespace LIDT.MIPStarRE.LDT.Pasting
end LIDT.MIPStarRE.LDT.Pasting
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

namespace LIDT

end LIDT

open LIDT
/-!
# Section 12 pasting: switcheroo second term

Complete-part self-consistency and the second switcheroo term.
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
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params))
        (fun y =>
          _root_.LIDT.MIPStarRE.LDT.Preliminaries.middleSandwichExpectation ψbi
            (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params))
            (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartProjFamily params family) (((M y).toSubMeas).total)) =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params)) (fun q =>
        _root_.LIDT.MIPStarRE.LDT.ev ψbi
          (_root_.LIDT.MIPStarRE.LDT.opTensor
            (((M q.2).toSubMeas).total)
            ((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total))) := by
  let 𝒟x : _root_.LIDT.MIPStarRE.LDT.Distribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params) :=
    _root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params)
  let Mtotal : _root_.LIDT.MIPStarRE.LDT.Fq params → _root_.LIDT.MIPStarRE.Quantum.Op ι := fun y =>
    ((M y).toSubMeas).total
  let Gtotal : _root_.LIDT.MIPStarRE.LDT.Fq params → _root_.LIDT.MIPStarRE.Quantum.Op ι := fun x =>
    (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family x).total
  let F : _root_.LIDT.MIPStarRE.LDT.Fq params → _root_.LIDT.MIPStarRE.LDT.Fq params → _root_.LIDT.MIPStarRE.LDT.Error := fun x y =>
    ∑ u : Unit,
      _root_.LIDT.MIPStarRE.LDT.ev ψbi
        (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (Mtotal y) *
          _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartProjFamily params family x).outcome u))
  calc
    _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟x (fun y =>
        _root_.LIDT.MIPStarRE.LDT.Preliminaries.middleSandwichExpectation ψbi 𝒟x
          (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartProjFamily params family) (((M y).toSubMeas).total))
      = _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟x (fun y => _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟x (fun x => F x y)) := by
        simp [F, 𝒟x, _root_.LIDT.MIPStarRE.LDT.Preliminaries.middleSandwichExpectation, Mtotal]
    _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params))
          (fun q => F q.2 q.1) := by
        symm
        simpa [𝒟x, _root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion, _root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion] using
          (_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_prod
            (α := _root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params)
            (β := _root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params)
            (f := fun y x => F x y))
    _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params))
          (fun q => F q.1 q.2) := by
        symm
        simpa [_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion] using
          (_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_equiv
            (α := _root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params)
            (β := _root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params)
            (Equiv.prodComm (_root_.LIDT.MIPStarRE.LDT.Fq params) (_root_.LIDT.MIPStarRE.LDT.Fq params))
            (fun q => F q.1 q.2))
    _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params)) (fun q =>
          _root_.LIDT.MIPStarRE.LDT.ev ψbi
            (_root_.LIDT.MIPStarRE.LDT.opTensor
              (((M q.2).toSubMeas).total)
              ((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total))) := by
        apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
        intro q
        rcases q with ⟨x, y⟩
        have hsingle :
            (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartProjFamily params family x).outcome () = Gtotal x := by
          change (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family x).outcome () =
            (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family x).total
          exact _root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas_outcome_unit params family x
        simp [F, Gtotal, Mtotal, hsingle, _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor]
