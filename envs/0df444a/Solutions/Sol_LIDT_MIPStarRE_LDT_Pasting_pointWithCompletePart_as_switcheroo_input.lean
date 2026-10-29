-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.pointWithCompletePart_as_switcheroo_input
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T16:55:34.50549+00:00
-- url     : https://prove2.me/submissions/77ba3eae-4223-4894-a075-7bdb21399bf5

-- Generated proof for MIPStarRE.LDT.Pasting.pointWithCompletePart_as_switcheroo_input.
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
# Section 12 pasting: switcheroo completion utilities

Post-theorem convenience lemmas: question-swapping, complete-part
reinterpretations, and self-consistency inheritance.
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters) [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (ψbi : _root_.LIDT.MIPStarRE.LDT.QuantumState (ι × ι))
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    (gamma : _root_.LIDT.MIPStarRE.LDT.Error)
    (hcomm : _root_.LIDT.MIPStarRE.LDT.SDDOpRel ψbi
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params))
      (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartPointProductLeft params family)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartPointProductRight params family)
      gamma) :
    _root_.LIDT.MIPStarRE.LDT.SDDOpRel ψbi
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params))
      (_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooPointProductLeft params family (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartProjFamily params family))
      (_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooPointProductRight params family (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartProjFamily params family))
      gamma := by
  rcases hcomm with ⟨hcomm⟩
  constructor
  unfold _root_.LIDT.MIPStarRE.LDT.sddErrorOp at *
  calc
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params))
        (fun q => _root_.LIDT.MIPStarRE.LDT.qSDDOp ψbi
          (_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooPointProductLeft params family (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartProjFamily params family) q)
          (_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooPointProductRight params family (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartProjFamily params family) q))
      = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params))
          (fun q => _root_.LIDT.MIPStarRE.LDT.qSDDOp ψbi
            (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartPointProductLeft params family q)
            (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartPointProductRight params family q)) := by
              apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
              intro q
              unfold _root_.LIDT.MIPStarRE.LDT.qSDDOp _root_.LIDT.MIPStarRE.LDT.qSDDCore
              let F : _root_.LIDT.MIPStarRE.LDT.Polynomial params × Unit → _root_.LIDT.MIPStarRE.LDT.Error := fun ab =>
                _root_.LIDT.MIPStarRE.LDT.ev ψbi
                  ((((_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooPointProductLeft params family
                            (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartProjFamily params family) q).outcome ab -
                          (_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooPointProductRight params family
                            (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartProjFamily params family) q).outcome ab)ᴴ) *
                      ((_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooPointProductLeft params family
                            (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartProjFamily params family) q).outcome ab -
                        (_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooPointProductRight params family
                          (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartProjFamily params family) q).outcome ab))
              change (∑ ab : _root_.LIDT.MIPStarRE.LDT.Polynomial params × Unit, F ab) = _
              have hsplit :
                  (∑ ab : _root_.LIDT.MIPStarRE.LDT.Polynomial params × Unit, F ab) =
                    ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, ∑ u : Unit, F (g, u) := by
                simpa [F] using
                  (Fintype.sum_prod_type' (f := fun g u => F (g, u)))
              have hsingle :
                  (_root_.LIDT.MIPStarRE.LDT.postprocess ((family.meas q.2).toSubMeas) (fun _ => ())).outcome () =
                    (family.meas q.2).total := by
                rw [← _root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas_total (params := params) (family := family) q.2]
                exact _root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas_outcome_unit
                  (params := params) (family := family) q.2
              rw [hsplit]
              simp [F, _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooPointProductLeft, _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooPointProductRight,
                _root_.LIDT.MIPStarRE.LDT.Pasting.completePartProjFamily, _root_.LIDT.MIPStarRE.LDT.Pasting.completePartPointProductLeft,
                _root_.LIDT.MIPStarRE.LDT.Pasting.completePartPointProductRight, _root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas,
                _root_.LIDT.MIPStarRE.LDT.Pasting.multiplyByTotalOnRight, _root_.LIDT.MIPStarRE.LDT.Pasting.multiplyByTotalOnLeft,
                _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.orderedProductOpFamily, _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.reversedProductOpFamily,
                _root_.LIDT.MIPStarRE.LDT.OpFamily.leftPlacedOpFamily, _root_.LIDT.MIPStarRE.LDT.postprocess_total,
                (family.meas q.2).sum_eq_total]
    _ ≤ gamma := hcomm
