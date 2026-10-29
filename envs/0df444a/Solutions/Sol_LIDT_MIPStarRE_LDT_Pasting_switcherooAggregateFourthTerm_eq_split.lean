-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFourthTerm_eq_split
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:03:35.630877+00:00
-- url     : https://prove2.me/submissions/89a003b7-6460-4986-b1b6-6a05f6737a35

-- Generated proof for MIPStarRE.LDT.Pasting.switcherooAggregateFourthTerm_eq_split.
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
# Section 12 pasting: switcheroo aggregate terms

The remaining switcheroo aggregate terms and split formulas.
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
    _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFourthTerm params ψbi family M =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params)) (fun q =>
        ∑ go : _root_.LIDT.MIPStarRE.LDT.Polynomial params × Outcome,
          _root_.LIDT.MIPStarRE.LDT.ev ψbi
            (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
              ((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total *
                (M q.2).outcome go.2 *
                (family.meas q.1).outcome go.1 *
                (family.meas q.1).outcome go.1 *
                (M q.2).outcome go.2))) := by
  unfold _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFourthTerm
  apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
  intro q
  let G : _root_.LIDT.MIPStarRE.Quantum.Op ι := (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total
  let Gq : _root_.LIDT.MIPStarRE.LDT.Polynomial params → _root_.LIDT.MIPStarRE.Quantum.Op ι := (family.meas q.1).outcome
  calc
    ∑ o : Outcome,
        _root_.LIDT.MIPStarRE.LDT.ev ψbi
          (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
            (G * (M q.2).outcome o * G * (M q.2).outcome o))
      = ∑ o : Outcome,
          _root_.LIDT.MIPStarRE.LDT.ev ψbi
            (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
              (G * (M q.2).outcome o * (∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, Gq g) *
                (M q.2).outcome o)) := by
            refine Finset.sum_congr rfl ?_
            intro o _
            rw [(family.meas q.1).sum_eq_total]
            simp [G]
    _ = ∑ o : Outcome,
          ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params,
            _root_.LIDT.MIPStarRE.LDT.ev ψbi
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                (G * (M q.2).outcome o * Gq g * (M q.2).outcome o)) := by
            refine Finset.sum_congr rfl ?_
            intro o _
            rw [← _root_.LIDT.MIPStarRE.LDT.ev_sum ψbi (fun g : _root_.LIDT.MIPStarRE.LDT.Polynomial params =>
              _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                (G * (M q.2).outcome o * Gq g * (M q.2).outcome o))]
            congr 1
            rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_finset_sum (ι₂ := ι) Finset.univ,
              Matrix.mul_sum, Finset.sum_mul]
    _ = ∑ o : Outcome,
          ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params,
            _root_.LIDT.MIPStarRE.LDT.ev ψbi
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                (G * (M q.2).outcome o * Gq g * Gq g * (M q.2).outcome o)) := by
            refine Finset.sum_congr rfl ?_
            intro o _
            refine Finset.sum_congr rfl ?_
            intro g _
            simp [Gq, mul_assoc, (family.meas q.1).proj g]
    _ = ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params,
          ∑ o : Outcome,
            _root_.LIDT.MIPStarRE.LDT.ev ψbi
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                (G * (M q.2).outcome o * Gq g * Gq g * (M q.2).outcome o)) := by
            rw [Finset.sum_comm]
    _ = ∑ go : _root_.LIDT.MIPStarRE.LDT.Polynomial params × Outcome,
          _root_.LIDT.MIPStarRE.LDT.ev ψbi
            (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
              (G * (M q.2).outcome go.2 * Gq go.1 * Gq go.1 * (M q.2).outcome go.2)) := by
            symm
            simpa using
              (Fintype.sum_prod_type' (f := fun g o =>
                _root_.LIDT.MIPStarRE.LDT.ev ψbi
                  (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                    (G * (M q.2).outcome o * Gq g * Gq g * (M q.2).outcome o))))
