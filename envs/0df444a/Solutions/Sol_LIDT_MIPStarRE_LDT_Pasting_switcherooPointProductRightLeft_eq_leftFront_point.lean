-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.switcherooPointProductRightLeft_eq_leftFront_point
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T16:51:31.592952+00:00
-- url     : https://prove2.me/submissions/8074af16-40ee-4383-97c2-8cc4e5b7a8a5

-- Generated proof for MIPStarRE.LDT.Pasting.switcherooPointProductRightLeft_eq_leftFront_point.
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

open scoped _root_.Matrix

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
    (M : _root_.LIDT.MIPStarRE.LDT.IdxProjSubMeas (_root_.LIDT.MIPStarRE.LDT.Fq params) Outcome ι)
    (q : _root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params)
    (go : _root_.LIDT.MIPStarRE.LDT.Polynomial params × Outcome) :
    _root_.LIDT.MIPStarRE.LDT.ev ψbi
      (((_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooPointProductRight params family M q).outcome go)ᴴ *
        (_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooPointProductLeft params family M q).outcome go) =
      _root_.LIDT.MIPStarRE.LDT.ev ψbi
        (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
          (((family.meas q.1).outcome go.1) *
            (M q.2).outcome go.2 *
            (family.meas q.1).outcome go.1 *
            (M q.2).outcome go.2)) := by
  let G : _root_.LIDT.MIPStarRE.Quantum.Op ι := (family.meas q.1).outcome go.1
  let Mo : _root_.LIDT.MIPStarRE.Quantum.Op ι := (M q.2).outcome go.2
  have hGherm : Gᴴ = G := (family.meas q.1).outcome_hermitian go.1
  have hMoherm : Moᴴ = Mo := (M q.2).outcome_hermitian go.2
  calc
    _root_.LIDT.MIPStarRE.LDT.ev ψbi
        (((_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooPointProductRight params family M q).outcome go)ᴴ *
          (_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooPointProductLeft params family M q).outcome go)
      = _root_.LIDT.MIPStarRE.LDT.ev ψbi ((_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (Mo * G))ᴴ * _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (G * Mo)) := by
          simp [_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooPointProductLeft, _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooPointProductRight,
            _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.orderedProductOpFamily, _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.reversedProductOpFamily,
            _root_.LIDT.MIPStarRE.LDT.OpFamily.leftPlacedOpFamily, G, Mo]
    _ = _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (((Mo * G)ᴴ) * (G * Mo))) := by
          rw [show (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (Mo * G))ᴴ =
              _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((Mo * G)ᴴ) by
                simpa [_root_.LIDT.MIPStarRE.LDT.leftTensor, _root_.LIDT.MIPStarRE.LDT.opTensor] using
                  (_root_.LIDT.MIPStarRE.LDT.conjTranspose_opTensor (Mo * G) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι))]
          rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_mul_leftTensor]
    _ = _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (G * Mo * G * Mo)) := by
          congr 1
          simp [Matrix.conjTranspose_mul, hGherm, hMoherm, mul_assoc]
    _ = _root_.LIDT.MIPStarRE.LDT.ev ψbi
          (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
            (((family.meas q.1).outcome go.1) *
              (M q.2).outcome go.2 *
              (family.meas q.1).outcome go.1 *
              (M q.2).outcome go.2)) := by
          simp [G, Mo]
