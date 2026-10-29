-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.avgOver_distinct_bounded_le_avgOver_uniform_add_tv_of_any_k
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T16:20:58.464122+00:00
-- url     : https://prove2.me/submissions/b5cdfca4-1650-442b-9fa4-8b67b66bee11

-- Generated proof for MIPStarRE.LDT.Pasting.avgOver_distinct_bounded_le_avgOver_uniform_add_tv_of_any_k.
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







/-- The number of injective `k`-tuples is the falling factorial `q(q-1) ... (q-k+1)`. -/
theorem distinctTupleSupport_card (params : Parameters) (k : ℕ) :
    (distinctTupleSupport params k).card = params.q.descFactorial k := by
  classical
  rw [← Fintype.card_coe]
  let e : { xs : PointTuple params k // Function.Injective xs } ≃ (Fin k ↪ Fq params) :=
    Equiv.subtypeInjectiveEquivEmbedding (Fin k) (Fq params)
  simpa [distinctTupleSupport, Finset.mem_filter] using
    (Fintype.card_congr e).trans Fintype.card_embedding_eq

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

/-- If `q < k`, no injective `k`-tuple of field elements exists. -/
theorem distinctTupleSupport_eq_empty_of_lt
    (params : Parameters) (k : ℕ) (hk : params.q < k) :
    distinctTupleSupport params k = ∅ := by
  apply Finset.card_eq_zero.mp
  rw [distinctTupleSupport_card]
  exact Nat.descFactorial_eq_zero_iff_lt.mpr hk























































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
# Line interpolation: averaging and tensor helpers

Tensor/average helper lemmas and total-variation comparison used across the
line interpolation error bounding chain.

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
    (k : ℕ)
    (F : _root_.LIDT.MIPStarRE.LDT.PointTuple params k → _root_.LIDT.MIPStarRE.LDT.Error)
    (hF_nonneg : ∀ xs, 0 ≤ F xs)
    (hF_le_one : ∀ xs, F xs ≤ 1) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.Pasting.distinctTupleDistribution params k) F
      ≤ _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params k)) F
        + _root_.LIDT.MIPStarRE.LDT.totalVariationDistance
            (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params k))
            (_root_.LIDT.MIPStarRE.LDT.Pasting.distinctTupleDistribution params k) := by
  classical
  by_cases hk : k ≤ params.q
  · exact _root_.LIDT.MIPStarRE.LDT.Pasting.avgOver_distinct_bounded_le_avgOver_uniform_add_tv params k hk F hF_nonneg hF_le_one
  · have hkq : params.q < k := lt_of_not_ge hk
    let support : Finset (_root_.LIDT.MIPStarRE.LDT.PointTuple params k) :=
      _root_.LIDT.MIPStarRE.LDT.Pasting.distinctTupleSupport params k
    have hsupport_card : support.card = params.q.descFactorial k := by
      simpa [support] using _root_.LIDT.MIPStarRE.LDT.Pasting.distinctTupleSupport_card params k
    have hsupport_empty : support = ∅ := by
      simpa [support] using _root_.LIDT.MIPStarRE.LDT.Pasting.distinctTupleSupport_eq_empty_of_lt params k hkq
    have hdistinct_zero : _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.Pasting.distinctTupleDistribution params k) F = 0 := by
      unfold _root_.LIDT.MIPStarRE.LDT.avgOver
      simp [_root_.LIDT.MIPStarRE.LDT.Pasting.distinctTupleDistribution, support, hsupport_empty]
    have hright_nonneg :
        0 ≤ _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params k)) F +
            _root_.LIDT.MIPStarRE.LDT.totalVariationDistance
              (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params k))
              (_root_.LIDT.MIPStarRE.LDT.Pasting.distinctTupleDistribution params k) := by
      have hunif_nonneg : 0 ≤ _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params k)) F := by
        unfold _root_.LIDT.MIPStarRE.LDT.avgOver
        exact Finset.sum_nonneg fun xs _ =>
          mul_nonneg ((_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params k)).nonnegative xs) (hF_nonneg xs)
      have htv_nonneg :
          0 ≤ _root_.LIDT.MIPStarRE.LDT.totalVariationDistance
            (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params k))
            (_root_.LIDT.MIPStarRE.LDT.Pasting.distinctTupleDistribution params k) := by
        unfold _root_.LIDT.MIPStarRE.LDT.totalVariationDistance
        positivity
      linarith
    rw [hdistinct_zero]
    exact hright_nonneg
