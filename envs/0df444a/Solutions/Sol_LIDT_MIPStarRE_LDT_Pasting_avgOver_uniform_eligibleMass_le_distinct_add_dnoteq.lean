-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.avgOver_uniform_eligibleMass_le_distinct_add_dnoteq
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T16:48:09.67076+00:00
-- url     : https://prove2.me/submissions/3a234917-979d-4bc5-a2aa-4d8dc2d6b32b

-- Generated proof for MIPStarRE.LDT.Pasting.avgOver_uniform_eligibleMass_le_distinct_add_dnoteq.
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_ldDnoteq
import Theorems.Thm_LIDT_MIPStarRE_LDT_avgOver_le_avgOver_add_totalVariationDistance

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

/- Source helpers from MIPStarRE/LDT/Basic/DistributionUniform.lean. -/
/-!
# Uniform subset estimates

This file contains estimates for the total variation distance between the
uniform distribution on a finite type and the uniform distribution on a
nonempty finite subset, together with averaging bounds for `[0,1]`-valued
functions.  The uniform-subset total-variation identity is proved by transport
through Mathlib probability mass functions.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.LDT



/-- A `[0,1]`-valued function averaged over a nonempty finite subset is bounded
by its ambient uniform average plus the total variation distance between the
two uniform distributions. -/
theorem avgOver_uniformOnFinset_le_uniformDistribution_add_totalVariationDistance
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (s : Finset α) (hs : s.Nonempty)
    (f : α → Error)
    (hf_nonneg : ∀ a, 0 ≤ f a)
    (hf_le_one : ∀ a, f a ≤ 1) :
    avgOver (Distribution.uniformOnFinset s) f
      ≤ avgOver (uniformDistribution α) f
        + totalVariationDistance (uniformDistribution α) (Distribution.uniformOnFinset s) := by
  exact
    avgOver_le_avgOver_add_totalVariationDistance
      (uniformDistribution α) (Distribution.uniformOnFinset s)
      (uniformDistribution_isProbability α)
      (Distribution.uniformOnFinset_isProbability s hs)
      f hf_nonneg hf_le_one

end MIPStarRE.LDT

end

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



















end MIPStarRE.LDT.Pasting

end

/- Source helpers from MIPStarRE/LDT/Pasting/Defs/Tuples.lean. -/
/-!
# Section 12 — Definitions: tuples and operators

Tuple distributions, type abbreviations, and basic operator helpers.
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]









/-- If `k ≤ q`, there exists an injective `k`-tuple. -/
theorem distinctTupleSupport_nonempty_of_le
    (params : Parameters) (k : ℕ) (hk : k ≤ params.q) :
    (distinctTupleSupport params k).Nonempty := by
  classical
  refine ⟨fun i => ⟨i.1, Nat.lt_of_lt_of_le i.2 hk⟩, ?_⟩
  refine Finset.mem_filter.mpr ?_
  constructor
  · simp
  · intro i j hij
    exact Fin.ext (by simpa using congrArg Fin.val hij)











/-- For `k ≤ q`, the distinct-tuple distribution is a probability distribution. -/
theorem distinctTupleDistribution_isProbability_of_le
    (params : Parameters) (k : ℕ) (hk : k ≤ params.q) :
    (distinctTupleDistribution params k).IsProbability := by
  simpa [distinctTupleDistribution] using
    Distribution.uniformOnFinset_isProbability (distinctTupleSupport params k)
      (distinctTupleSupport_nonempty_of_le params k hk)



/-- For `k ≤ q`, the weights of the distinct-tuple distribution sum to one. -/
theorem distinctTupleDistribution_weight_sum_eq_one_of_le
    (params : Parameters) (k : ℕ) (hk : k ≤ params.q) :
    ∑ xs ∈ (distinctTupleDistribution params k).support,
      (distinctTupleDistribution params k).weight xs = 1 :=
  (distinctTupleDistribution_isProbability_of_le params k hk).weight_sum_eq_one









































end MIPStarRE.LDT.Pasting

end

/- Source helpers from MIPStarRE/LDT/Pasting/ComparisonLemmas/LineInterpolation/Averaging.lean. -/
/-!
# Line interpolation: averaging and tensor helpers

Tensor/average helper lemmas and total-variation comparison used across the
line interpolation error bounding chain.

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

lemma avgOver_distinct_bounded_le_avgOver_uniform_add_tv
    (params : Parameters) [FieldModel params.q]
    (k : ℕ) (hk : k ≤ params.q)
    (F : PointTuple params k → Error)
    (hF_nonneg : ∀ xs, 0 ≤ F xs)
    (hF_le_one : ∀ xs, F xs ≤ 1) :
    avgOver (distinctTupleDistribution params k) F
      ≤ avgOver (uniformDistribution (PointTuple params k)) F
        + totalVariationDistance
            (uniformDistribution (PointTuple params k))
            (distinctTupleDistribution params k) := by
  simpa [distinctTupleDistribution] using
    avgOver_uniformOnFinset_le_uniformDistribution_add_totalVariationDistance
      (s := distinctTupleSupport params k)
      (distinctTupleSupport_nonempty_of_le params k hk) F hF_nonneg hF_le_one















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
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params k)) (fun xs =>
        _root_.LIDT.MIPStarRE.LDT.subMeasMass strategy.state
          ((_root_.LIDT.MIPStarRE.LDT.Pasting.interpolationEligibleSandwichFamily params family k xs).liftLeft)) ≤
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.Pasting.distinctTupleDistribution params k) (fun xs =>
        _root_.LIDT.MIPStarRE.LDT.subMeasMass strategy.state
          ((_root_.LIDT.MIPStarRE.LDT.Pasting.interpolationEligibleSandwichFamily params family k xs).liftLeft)) +
        ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error) := by
  classical
  let F : _root_.LIDT.MIPStarRE.LDT.PointTuple params k → _root_.LIDT.MIPStarRE.LDT.Error := fun xs =>
    _root_.LIDT.MIPStarRE.LDT.subMeasMass strategy.state
      ((_root_.LIDT.MIPStarRE.LDT.Pasting.interpolationEligibleSandwichFamily params family k xs).liftLeft)
  by_cases hk : k ≤ params.q
  · let G : _root_.LIDT.MIPStarRE.LDT.PointTuple params k → _root_.LIDT.MIPStarRE.LDT.Error := fun xs => 1 - F xs
    have hG_nonneg : ∀ xs, 0 ≤ G xs := by
      intro xs
      dsimp [G]
      exact sub_nonneg.mpr (_root_.LIDT.MIPStarRE.LDT.Pasting.eligibleMass_le_one params strategy family xs)
    have hG_le_one : ∀ xs, G xs ≤ 1 := by
      intro xs
      dsimp [G]
      have hF_nonneg := eligibleMass_nonneg params strategy family xs
      linarith
    have hcomp := _root_.LIDT.MIPStarRE.LDT.Pasting.avgOver_distinct_bounded_le_avgOver_uniform_add_tv params k hk
      G hG_nonneg hG_le_one
    have hDconst :
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.Pasting.distinctTupleDistribution params k) (fun _ : _root_.LIDT.MIPStarRE.LDT.PointTuple params k => 1) =
          1 := by
      unfold _root_.LIDT.MIPStarRE.LDT.avgOver
      simpa using _root_.LIDT.MIPStarRE.LDT.Pasting.distinctTupleDistribution_weight_sum_eq_one_of_le params k hk
    have hUconst : _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params k))
        (fun _ : _root_.LIDT.MIPStarRE.LDT.PointTuple params k => 1) = 1 := by
      simpa using _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_const (α := _root_.LIDT.MIPStarRE.LDT.PointTuple params k) (1 : _root_.LIDT.MIPStarRE.LDT.Error)
    have hDsub : _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.Pasting.distinctTupleDistribution params k) G = 1 -
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.Pasting.distinctTupleDistribution params k) F := by
      dsimp [G]
      rw [_root_.LIDT.MIPStarRE.LDT.avgOver_sub, hDconst]
    have hUsub : _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params k)) G = 1 -
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params k)) F := by
      dsimp [G]
      rw [_root_.LIDT.MIPStarRE.LDT.avgOver_sub, hUconst]
    have htv := _root_.LIDT.MIPStarRE.LDT.Pasting.ldDnoteq params k
    dsimp [F] at hcomp hDsub hUsub ⊢
    rw [hDsub, hUsub] at hcomp
    linarith
  · have hkq : params.q < k := lt_of_not_ge hk
    have hUle : _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params k)) F ≤ 1 := by
      exact _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_le_const F (1 : _root_.LIDT.MIPStarRE.LDT.Error) fun xs =>
        _root_.LIDT.MIPStarRE.LDT.Pasting.eligibleMass_le_one params strategy family xs
    have hDnonneg : 0 ≤ _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.Pasting.distinctTupleDistribution params k) F := by
      unfold _root_.LIDT.MIPStarRE.LDT.avgOver F
      exact Finset.sum_nonneg fun xs _ =>
        mul_nonneg ((_root_.LIDT.MIPStarRE.LDT.Pasting.distinctTupleDistribution params k).nonnegative xs)
          (eligibleMass_nonneg params strategy family xs)
    have hq_pos : (0 : _root_.LIDT.MIPStarRE.LDT.Error) < params.q := by exact_mod_cast params.hq
    have hk_cast : (params.q : _root_.LIDT.MIPStarRE.LDT.Error) < k := by exact_mod_cast hkq
    have hterm_ge_one : (1 : _root_.LIDT.MIPStarRE.LDT.Error) ≤ ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error) := by
      rw [le_div_iff₀ hq_pos]
      have hk_ge_one : (1 : _root_.LIDT.MIPStarRE.LDT.Error) ≤ k := by
        exact_mod_cast Nat.succ_le_of_lt (Nat.lt_trans params.hq hkq)
      have hq_le_k : (params.q : _root_.LIDT.MIPStarRE.LDT.Error) ≤ k := le_of_lt hk_cast
      nlinarith
    dsimp [F] at hUle hDnonneg ⊢
    linarith
