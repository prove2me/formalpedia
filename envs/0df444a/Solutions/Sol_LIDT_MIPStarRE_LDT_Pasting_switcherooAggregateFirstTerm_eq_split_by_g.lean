-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFirstTerm_eq_split_by_g
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T16:55:34.42199+00:00
-- url     : https://prove2.me/submissions/47822831-7ef1-45c2-b797-697f70f58321

-- Generated proof for MIPStarRE.LDT.Pasting.switcherooAggregateFirstTerm_eq_split_by_g.
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
# Section 12 pasting: switcheroo commuted contraction

The once-commuted contraction steps and the split-by-`g` rewrite.
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
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params)) (fun q =>
      ∑ go : _root_.LIDT.MIPStarRE.LDT.Polynomial params × Outcome,
        _root_.LIDT.MIPStarRE.LDT.ev ψbi
          (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
            ((M q.2).outcome go.2 *
              (family.meas q.1).outcome go.1 *
              (M q.2).outcome go.2))) =
      _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFirstTerm params ψbi family M := by
  calc
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params)) (fun q =>
      ∑ go : _root_.LIDT.MIPStarRE.LDT.Polynomial params × Outcome,
        _root_.LIDT.MIPStarRE.LDT.ev ψbi
          (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
            ((M q.2).outcome go.2 *
              (family.meas q.1).outcome go.1 *
              (M q.2).outcome go.2)))
      = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params)) (fun q =>
          ∑ o : Outcome,
            _root_.LIDT.MIPStarRE.LDT.ev ψbi
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                ((M q.2).outcome o *
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total *
                  (M q.2).outcome o))) := by
            apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
            intro q
            calc
              ∑ go : _root_.LIDT.MIPStarRE.LDT.Polynomial params × Outcome,
                  _root_.LIDT.MIPStarRE.LDT.ev ψbi
                    (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                      ((M q.2).outcome go.2 *
                        (family.meas q.1).outcome go.1 *
                        (M q.2).outcome go.2))
                = ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params,
                    ∑ o : Outcome,
                      _root_.LIDT.MIPStarRE.LDT.ev ψbi
                        (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                          ((M q.2).outcome o *
                            (family.meas q.1).outcome g *
                            (M q.2).outcome o)) := by
                      simpa using
                        (Fintype.sum_prod_type' (f := fun g o =>
                          _root_.LIDT.MIPStarRE.LDT.ev ψbi
                            (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                              ((M q.2).outcome o *
                                (family.meas q.1).outcome g *
                                (M q.2).outcome o))))
              _ = ∑ o : Outcome,
                    ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params,
                      _root_.LIDT.MIPStarRE.LDT.ev ψbi
                        (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                          ((M q.2).outcome o *
                            (family.meas q.1).outcome g *
                            (M q.2).outcome o)) := by
                      rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro o _
            calc
              ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params,
                  _root_.LIDT.MIPStarRE.LDT.ev ψbi
                    (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                      ((M q.2).outcome o * (family.meas q.1).outcome g * (M q.2).outcome o))
                = _root_.LIDT.MIPStarRE.LDT.ev ψbi
                    (∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params,
                      _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                        ((M q.2).outcome o * (family.meas q.1).outcome g * (M q.2).outcome o)) := by
                    rw [← _root_.LIDT.MIPStarRE.LDT.ev_sum ψbi]
              _ = _root_.LIDT.MIPStarRE.LDT.ev ψbi
                    (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                      (∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params,
                        (M q.2).outcome o * (family.meas q.1).outcome g * (M q.2).outcome o)) := by
                    rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_finset_sum (ι₂ := ι) Finset.univ]
              _ = _root_.LIDT.MIPStarRE.LDT.ev ψbi
                    (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                      ((M q.2).outcome o * (∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, (family.meas q.1).outcome g) *
                        (M q.2).outcome o)) := by
                    congr 1
                    simp [mul_assoc, Matrix.mul_sum, Finset.sum_mul]
              _ = _root_.LIDT.MIPStarRE.LDT.ev ψbi
                    (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                      ((M q.2).outcome o * (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total *
                        (M q.2).outcome o)) := by
                    rw [(family.meas q.1).sum_eq_total]
                    simp [_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas, _root_.LIDT.MIPStarRE.LDT.postprocess_total]
    _ = _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFirstTerm params ψbi family M := by
          unfold _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFirstTerm
          rfl
