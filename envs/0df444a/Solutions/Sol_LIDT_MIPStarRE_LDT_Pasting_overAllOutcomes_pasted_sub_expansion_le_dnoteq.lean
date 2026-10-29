-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.overAllOutcomes_pasted_sub_expansion_le_dnoteq
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T16:48:09.556571+00:00
-- url     : https://prove2.me/submissions/be3d3837-f645-4a14-b860-c383a1a98eb4

-- Generated proof for MIPStarRE.LDT.Pasting.overAllOutcomes_pasted_sub_expansion_le_dnoteq.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_SharedHelpers_SharedLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Normalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Stability
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_EvaluatedSliceBounds_PhaseOneThree
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_GCommStability_Scalar_First
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_GCommStability_Scalar_RawSecond
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Main_Auxiliary_HEvalTransport
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Main_Auxiliary_ScalarMarginalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Products
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_PaperChainPhaseFive
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_ProcessedG_MainChain
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_ProcessedG_PhaseTwo
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Averages
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Marginalization_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Marginalization_Y
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Normalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_Pullback
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_BackChain
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_Base
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_Chain
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_FlatChain
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_Lifting
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_Setup_Definitions
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_CSSetup
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_Endpoint
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_EndpointEquivs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_PrefixMoved
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LineInterpolation_BadLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LineInterpolation_BadMass
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LineInterpolation_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Core_LdGbcon
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CompletionTransfer
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_PolynomialAgreement
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SelfConsistency_Extensions
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_ApproxDelta
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Triangles_Core
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
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.RingTheory.MvPolynomial.Basic
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_avgOver_distinct_bounded_le_avgOver_uniform_add_tv_of_any_k
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_ldDnoteq

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Commutativity
end LIDT.MIPStarRE.LDT.Commutativity
namespace LIDT.MIPStarRE.LDT.Commutativity.GCommStability.Scalar
end LIDT.MIPStarRE.LDT.Commutativity.GCommStability.Scalar
namespace LIDT.MIPStarRE.LDT.CommutativityPoints
end LIDT.MIPStarRE.LDT.CommutativityPoints
namespace LIDT.MIPStarRE.LDT.Pasting
end LIDT.MIPStarRE.LDT.Pasting
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

namespace LIDT

/- Source helpers from MIPStarRE/LDT/Pasting/ComparisonLemmas/OverAllOutcomes/ErrorAndMass.lean. -/
/-!
# Section 12 pasting: over all outcomes — error terms and eligible mass

Error-arithmetic lemmas, eligible-mass bounds, and mass identities that feed the final
`lem:over-all-outcomes` comparison.

## References

- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]





/-- Eligible interpolation mass is nonnegative for every point tuple. -/
private lemma eligibleMass_nonneg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) {k : ℕ} (xs : PointTuple params k) :
    0 ≤ subMeasMass strategy.state
      ((interpolationEligibleSandwichFamily params family k xs).liftLeft) := by
  unfold subMeasMass SubMeas.liftLeft
  exact ev_nonneg_of_psd strategy.state _ <|
    leftTensor_nonneg (ι₂ := ι)
      (SubMeas.total_nonneg (interpolationEligibleSandwichFamily params family k xs))

/-- Eligible interpolation mass is at most one for every point tuple. -/
lemma eligibleMass_le_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) {k : ℕ} (xs : PointTuple params k) :
    subMeasMass strategy.state
      ((interpolationEligibleSandwichFamily params family k xs).liftLeft) ≤ 1 := by
  unfold subMeasMass SubMeas.liftLeft
  have hle :
      leftTensor (ι₂ := ι)
        (interpolationEligibleSandwichFamily params family k xs).total ≤
        (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
    exact leftTensor_le_one (ι₂ := ι)
      (interpolationEligibleSandwichFamily params family k xs).total_le_one
  simpa [ev_one_of_isNormalized strategy.state strategy.isNormalized] using
    ev_mono strategy.state _ _ hle

/-- Distinct tuple averaging is bounded by uniform averaging plus `ldDnoteq`. -/
private lemma avgOver_distinct_eligibleMass_le_uniform_add_dnoteq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ) :
    avgOver (distinctTupleDistribution params k) (fun xs =>
        subMeasMass strategy.state
          ((interpolationEligibleSandwichFamily params family k xs).liftLeft)) ≤
      avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
        subMeasMass strategy.state
          ((interpolationEligibleSandwichFamily params family k xs).liftLeft)) +
        ((k : Error) ^ (2 : ℕ)) / (params.q : Error) := by
  calc
    avgOver (distinctTupleDistribution params k) (fun xs =>
        subMeasMass strategy.state
          ((interpolationEligibleSandwichFamily params family k xs).liftLeft))
      ≤ avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
          subMeasMass strategy.state
            ((interpolationEligibleSandwichFamily params family k xs).liftLeft)) +
          totalVariationDistance
            (uniformDistribution (PointTuple params k))
            (distinctTupleDistribution params k) := by
          exact avgOver_distinct_bounded_le_avgOver_uniform_add_tv_of_any_k params k
            (fun xs => subMeasMass strategy.state
              ((interpolationEligibleSandwichFamily params family k xs).liftLeft))
            (eligibleMass_nonneg params strategy family)
            (eligibleMass_le_one params strategy family)
    _ ≤ avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
          subMeasMass strategy.state
            ((interpolationEligibleSandwichFamily params family k xs).liftLeft)) +
        ((k : Error) ^ (2 : ℕ)) / (params.q : Error) := by
          gcongr
          exact ldDnoteq params k



/-- The pasted mass is the distinct average of globally consistent eligible mass. -/
lemma overAllOutcomesPastedMass_eq_avg_distinct_global
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ) :
    overAllOutcomesPastedMass params strategy family k =
      avgOver (distinctTupleDistribution params k) (fun xs =>
        subMeasMass strategy.state
          ((restrictSubMeas (interpolationEligibleSandwichFamily params family k xs)
            (IsGloballyConsistent params xs)).liftLeft)) := by
  simp only [overAllOutcomesPastedMass, constructedPastedSubMeas, pastedInterpolationFamily,
    subMeasMass, SubMeas.liftLeft, averageIdxSubMeas, postprocess_total]
  exact ev_leftTensor_averageOperatorOverDistribution strategy.state
    (distinctTupleDistribution params k)
    (fun xs =>
      (restrictSubMeas (interpolationEligibleSandwichFamily params family k xs)
        (IsGloballyConsistent params xs)).total)

/-- The expansion mass is the uniform average of eligible interpolation mass. -/
lemma overAllOutcomesExpansionMass_eq_avg_uniform_eligible
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ) :
    overAllOutcomesExpansionMass params strategy family k =
      avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
        subMeasMass strategy.state
          ((interpolationEligibleSandwichFamily params family k xs).liftLeft)) := by
  simp only [overAllOutcomesExpansionMass, allOutcomesExpansionFamily,
    averagedEligibleSandwichSubMeas, pastedMeasurementTotal, constSubMeasFamily,
    subMeasMass, SubMeas.liftLeft, IdxSubMeas.liftLeft, averageIdxSubMeas]
  exact ev_leftTensor_averageOperatorOverDistribution strategy.state
    (uniformDistribution (PointTuple params k))
    (fun xs => (interpolationEligibleSandwichFamily params family k xs).total)











end MIPStarRE.LDT.Pasting

end

/- Source helpers from MIPStarRE/LDT/Pasting/Sandwich/GHatSandwich.lean. -/
/-!
# Section 12 — Sandwich constructions: `GHat` sandwich families

Completed-slice sandwich families and restriction helpers.
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

universe u v

variable {ι : Type u} [Fintype ι] [DecidableEq ι]











/-- Restricting a submeasurement can only decrease its total operator. -/
lemma restrictSubMeas_total_le_total {α : Type*} [Fintype α]
    (A : SubMeas α ι) (p : α → Prop) [DecidablePred p] :
    (restrictSubMeas A p).total ≤ A.total := by
  calc
    (restrictSubMeas A p).total = ∑ a ∈ Finset.univ.filter p, A.outcome a := rfl
    _ ≤ ∑ a : α, A.outcome a := by
      exact Finset.sum_le_univ_sum_of_nonneg
        (s := Finset.univ.filter p)
        (w := fun a => A.outcome_pos a)
    _ = A.total := A.sum_eq_total







end MIPStarRE.LDT.Pasting

end

end LIDT

open LIDT
/-!
# Section 12 pasting: over all outcomes — error terms and eligible mass

Error-arithmetic lemmas, eligible-mass bounds, and mass identities that feed the final
`lem:over-all-outcomes` comparison.

## References

- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
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
    (strategy : _root_.LIDT.MIPStarRE.LDT.SymStrat params.next ι)
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι) (k : ℕ) :
    _root_.LIDT.MIPStarRE.LDT.Pasting.overAllOutcomesPastedMass params strategy family k -
        _root_.LIDT.MIPStarRE.LDT.Pasting.overAllOutcomesExpansionMass params strategy family k ≤
      ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error) := by
  have hdist :
      _root_.LIDT.MIPStarRE.LDT.Pasting.overAllOutcomesPastedMass params strategy family k ≤
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.Pasting.distinctTupleDistribution params k) (fun xs =>
          _root_.LIDT.MIPStarRE.LDT.subMeasMass strategy.state
            ((_root_.LIDT.MIPStarRE.LDT.Pasting.interpolationEligibleSandwichFamily params family k xs).liftLeft)) := by
    rw [_root_.LIDT.MIPStarRE.LDT.Pasting.overAllOutcomesPastedMass_eq_avg_distinct_global]
    exact _root_.LIDT.MIPStarRE.LDT.avgOver_mono _ _ _ fun xs => by
      unfold _root_.LIDT.MIPStarRE.LDT.subMeasMass _root_.LIDT.MIPStarRE.LDT.SubMeas.liftLeft
      exact _root_.LIDT.MIPStarRE.LDT.ev_mono strategy.state _ _ <| by
        simpa [_root_.LIDT.MIPStarRE.LDT.leftTensor, _root_.LIDT.MIPStarRE.LDT.opTensor] using
          (_root_.LIDT.MIPStarRE.LDT.opTensor_mono_left (ι₂ := ι) (B := (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι))
            (_root_.LIDT.MIPStarRE.LDT.Pasting.restrictSubMeas_total_le_total
              (_root_.LIDT.MIPStarRE.LDT.Pasting.interpolationEligibleSandwichFamily params family k xs)
              (_root_.LIDT.MIPStarRE.LDT.Pasting.IsGloballyConsistent params xs))
            (show 0 ≤ (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) by simp))
  have hswap := avgOver_distinct_eligibleMass_le_uniform_add_dnoteq
    params strategy family k
  rw [_root_.LIDT.MIPStarRE.LDT.Pasting.overAllOutcomesExpansionMass_eq_avg_uniform_eligible]
  linarith
