-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateMixedScalar_close_leftFrontScalar
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:11:33.133023+00:00
-- url     : https://prove2.me/submissions/54076283-7c07-4835-a9f3-0dbc0fcfcf96

-- Generated proof for MIPStarRE.LDT.Pasting.switcherooAggregateMixedScalar_close_leftFrontScalar.
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_switcherooAggregateFourthTerm_mixed_close_left_front_scalar

namespace LIDT.MIPStarRE.LDT.Pasting
end LIDT.MIPStarRE.LDT.Pasting
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

namespace LIDT

/- Source helpers from MIPStarRE/LDT/Pasting/SwitcherooCompletion/FourthTermChain.lean. -/
/-!
# Section 12 pasting: fourth-term chain helpers

Internal helpers by convention for the fourth-term chain in `commutativitySwitcheroo`.
These were extracted from `SwitcherooCompletion` to keep that file under
the 1000-line threshold.
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Pointwise identity rewriting the mixed scalar expression into right/left tensor order. -/
lemma switcherooAggregateMixedScalar_point
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι)
    (q : SlicePairQuestion params) :
    (∑ g : Polynomial params, ∑ o : Outcome,
        ev ψbi
          (rightTensor (ι₁ := ι) ((family.meas q.1).outcome g) *
            leftTensor (ι₂ := ι)
              ((completePartSubMeas params family q.1).total *
                (M q.2).outcome o *
                (family.meas q.1).outcome g *
                (M q.2).outcome o))) =
      ∑ g : Polynomial params, ∑ o : Outcome,
        ev ψbi
          ((leftTensor (ι₂ := ι)
            ((completePartSubMeas params family q.1).total *
              (M q.2).outcome o *
              (family.meas q.1).outcome g *
              (M q.2).outcome o)) *
            rightTensor (ι₁ := ι) ((family.meas q.1).outcome g)) := by
  refine Finset.sum_congr rfl ?_
  intro g _
  refine Finset.sum_congr rfl ?_
  intro o _
  rw [rightTensor_mul_leftTensor_eq_opTensor, leftTensor_mul_rightTensor_eq_opTensor]







-- The last `χ`-step needs only pointwise normalization for the `G_g M_o`
-- factors inside `closenessOfInnerProduct_right`; the heavy adjoint rewrites are
-- isolated in the two pointwise helper lemmas above.


end MIPStarRE.LDT.Pasting

end

end LIDT

open LIDT
/-!
# Section 12 pasting: fourth-term chain helpers

Internal helpers by convention for the fourth-term chain in `commutativitySwitcheroo`.
These were extracted from `SwitcherooCompletion` to keep that file under
the 1000-line threshold.
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
    (hnorm : ψbi.IsNormalized)
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    (M : _root_.LIDT.MIPStarRE.LDT.IdxProjSubMeas (_root_.LIDT.MIPStarRE.LDT.Fq params) Outcome ι)
    (zeta : _root_.LIDT.MIPStarRE.LDT.Error)
    (hselfG : _root_.LIDT.MIPStarRE.LDT.Pasting.GCompleteSelfConsistencyStatement params ψbi family zeta) :
    |_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateMixedScalar params ψbi family M -
        _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateLeftFrontScalar params ψbi family M| ≤ Real.sqrt zeta := by
  have hleft :
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params)) (fun q =>
          ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, ∑ o : Outcome,
            _root_.LIDT.MIPStarRE.LDT.ev ψbi
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((family.meas q.1).outcome g) *
                _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                  ((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total *
                    (M q.2).outcome o *
                    (family.meas q.1).outcome g *
                    (M q.2).outcome o))) =
        _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateLeftFrontScalar params ψbi family M := by
    unfold _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateLeftFrontScalar
    apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
    intro q
    calc
      ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, ∑ o : Outcome,
          _root_.LIDT.MIPStarRE.LDT.ev ψbi
            (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((family.meas q.1).outcome g) *
              _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                ((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total *
                  (M q.2).outcome o *
                  (family.meas q.1).outcome g *
                  (M q.2).outcome o))
        = ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, ∑ o : Outcome,
            _root_.LIDT.MIPStarRE.LDT.ev ψbi
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                ((family.meas q.1).outcome g *
                  (M q.2).outcome o *
                  (family.meas q.1).outcome g *
                  (M q.2).outcome o)) := by
              refine Finset.sum_congr rfl ?_
              intro g _
              refine Finset.sum_congr rfl ?_
              intro o _
              have htotal :
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total = (family.meas q.1).total := by
                simp [_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas, _root_.LIDT.MIPStarRE.LDT.postprocess_total]
              calc
                _root_.LIDT.MIPStarRE.LDT.ev ψbi
                    (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((family.meas q.1).outcome g) *
                      _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                        ((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total *
                          (M q.2).outcome o *
                          (family.meas q.1).outcome g *
                          (M q.2).outcome o))
                  = _root_.LIDT.MIPStarRE.LDT.ev ψbi
                      (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                        ((family.meas q.1).outcome g *
                          (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total *
                          (M q.2).outcome o *
                          (family.meas q.1).outcome g *
                          (M q.2).outcome o)) := by
                            simp [_root_.LIDT.MIPStarRE.LDT.leftTensor_mul_leftTensor, mul_assoc]
                _ = _root_.LIDT.MIPStarRE.LDT.ev ψbi
                      (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                        (((family.meas q.1).outcome g * (family.meas q.1).total) *
                          (M q.2).outcome o *
                          (family.meas q.1).outcome g *
                          (M q.2).outcome o)) := by
                            rw [htotal]
                _ = _root_.LIDT.MIPStarRE.LDT.ev ψbi
                      (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                        ((family.meas q.1).outcome g *
                          (M q.2).outcome o *
                          (family.meas q.1).outcome g *
                          (M q.2).outcome o)) := by
                            rw [_root_.LIDT.MIPStarRE.LDT.Preliminaries.projSubMeas_outcome_mul_total_eq_outcome
                              (family.meas q.1) g]
      _ = ∑ go : _root_.LIDT.MIPStarRE.LDT.Polynomial params × Outcome,
            _root_.LIDT.MIPStarRE.LDT.ev ψbi
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                ((family.meas q.1).outcome go.1 *
                  (M q.2).outcome go.2 *
                  (family.meas q.1).outcome go.1 *
                  (M q.2).outcome go.2)) := by
              let f : _root_.LIDT.MIPStarRE.LDT.Polynomial params → Outcome → _root_.LIDT.MIPStarRE.LDT.Error := fun g o =>
                _root_.LIDT.MIPStarRE.LDT.ev ψbi
                  (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                    ((family.meas q.1).outcome g *
                      (M q.2).outcome o *
                      (family.meas q.1).outcome g *
                      (M q.2).outcome o))
              change (∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, ∑ o : Outcome, f g o) =
                ∑ go : _root_.LIDT.MIPStarRE.LDT.Polynomial params × Outcome, f go.1 go.2
              simpa using (Fintype.sum_prod_type' (f := f)).symm
  have hright :
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params)) (fun q =>
          ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, ∑ o : Outcome,
            _root_.LIDT.MIPStarRE.LDT.ev ψbi
              (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((family.meas q.1).outcome g) *
                _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                  ((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total *
                    (M q.2).outcome o *
                    (family.meas q.1).outcome g *
                    (M q.2).outcome o))) =
        _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateMixedScalar params ψbi family M := by
    unfold _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateMixedScalar
    apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
    intro q
    simpa [_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateMixedScalar] using
      _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateMixedScalar_point params ψbi family M q
  calc
    |_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateMixedScalar params ψbi family M -
        _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateLeftFrontScalar params ψbi family M|
      = |_root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params)) (fun q =>
            ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, ∑ o : Outcome,
              _root_.LIDT.MIPStarRE.LDT.ev ψbi
                (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((family.meas q.1).outcome g) *
                  _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                    ((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total *
                      (M q.2).outcome o *
                      (family.meas q.1).outcome g *
                      (M q.2).outcome o))) -
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params)) (fun q =>
            ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, ∑ o : Outcome,
              _root_.LIDT.MIPStarRE.LDT.ev ψbi
                (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((family.meas q.1).outcome g) *
                  _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                    ((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total *
                      (M q.2).outcome o *
                      (family.meas q.1).outcome g *
                      (M q.2).outcome o)))| := by
            rw [hleft, hright, abs_sub_comm]
    _ ≤ Real.sqrt zeta :=
      _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFourthTerm_mixed_close_left_front_scalar
          params ψbi hnorm family M zeta hselfG
