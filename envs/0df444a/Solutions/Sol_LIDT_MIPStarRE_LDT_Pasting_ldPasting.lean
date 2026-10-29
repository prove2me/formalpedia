-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.ldPasting
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T18:23:18.369548+00:00
-- url     : https://prove2.me/submissions/efa06b21-2470-4a67-b400-ea090b951a1e

-- Generated proof for MIPStarRE.LDT.Pasting.ldPasting.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_AdjacentStages_Chain_FinalMove
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_AdjacentStages_Chain_HalfSandwich
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_AdjacentStages_StageA0M1
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_Core_BernoulliTail
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_Core_FactBundles
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_MoveLemmas_Basic
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_PaperBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_Scalar
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_OverAllOutcomes_NonglobalDecomposition
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
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.RingTheory.MvPolynomial.Basic
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_degreeZeroPastedPointConsistency
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_ldPastingNontrivial
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_one_le_ldPastingError_of_one_le_nu
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_one_le_ldPastingNu_of_large_degreeRatio
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_one_le_ldPastingNu_of_large_gamma
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_one_le_ldPastingNu_of_large_zeta

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

/- Source helpers from MIPStarRE/LDT/Pasting/Bernoulli/ScalarBounds.lean. -/
/-!
# Section 12 pasting: scalar bounds for complementary Bernoulli branches

This file collects the elementary scalar estimates used by the complementary
branches of `thm:ld-pasting`.  These estimates correspond to the large-error
reduction in `references/ldt-paper/ld-pasting.tex`, lines 52--55.
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The scalar `κ` in a complete family is nonnegative. -/
lemma kappa_nonneg_of_complete
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {kappa : Error}
    (hcomplete : family.Complete strategy.state kappa) :
    0 ≤ kappa := by
  have hmass_le_one : subMeasMass strategy.state family.averagedSubMeas.liftLeft ≤ 1 := by
    unfold subMeasMass SubMeas.liftLeft
    have hle : leftTensor (ι₂ := ι) (IdxPolyFamily.averagedSubMeas family).total ≤
        (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
      exact leftTensor_le_one (ι₂ := ι) (IdxPolyFamily.averagedSubMeas family).total_le_one
    simpa [ev_one_of_isNormalized strategy.state strategy.isNormalized] using
      ev_mono strategy.state _ _ hle
  have hlower := hcomplete.averageCompleteness.lowerBound
  linarith

/-- The coefficient multiplying `κ` in the pasting error is nonnegative. -/
lemma ldPasting_kappa_coefficient_nonneg (params : Parameters) :
    0 ≤ (1 : Error) + 1 / (100 * (params.m : Error)) := by
  have hm_one : (1 : Error) ≤ (params.m : Error) := by exact_mod_cast params.hm
  have hm_pos : (0 : Error) < (params.m : Error) := lt_of_lt_of_le zero_lt_one hm_one
  have hden_pos : (0 : Error) < 100 * (params.m : Error) := by positivity
  have hfrac_nonneg : 0 ≤ (1 : Error) / (100 * (params.m : Error)) :=
    div_nonneg zero_le_one hden_pos.le
  linarith









/-- If `k = 0`, the exponential term alone gives the trivial pasting bound. -/
lemma one_le_ldPastingError_of_k_eq_zero
    (params : Parameters)
    (k : ℕ)
    (eps delta gamma kappa zeta : Error)
    (hkappa_nonneg : 0 ≤ kappa)
    (hk_zero : k = 0) :
    1 ≤ MainInductionStep.ldPastingInInductionError params k
      eps delta gamma kappa zeta := by
  subst k
  have hkappa_term_nonneg :
      0 ≤ kappa * (1 + 1 / (100 * (params.m : Error))) :=
    mul_nonneg hkappa_nonneg (ldPasting_kappa_coefficient_nonneg params)
  have hkappa_term_nonneg' :
      0 ≤ kappa * (1 + ((params.m : Error))⁻¹ * 100⁻¹) := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hkappa_term_nonneg
  simp [MainInductionStep.ldPastingInInductionError,
    MainInductionStep.ldPastingInInductionNu]
  nlinarith







end MIPStarRE.LDT.Pasting

end

/- Source helpers from MIPStarRE/LDT/Pasting/ComparisonLemmas/Common.lean. -/
/-!
# Section 12 pasting: comparison common helpers

Shared postprocessing, symmetry, distribution, boundedness, and arithmetic helpers for the Section
12 comparison lemmas.

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







lemma qBipartiteMatchMass_nonneg
    {Outcome : Type*} [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (A B : SubMeas Outcome ι) :
    0 ≤ qBipartiteMatchMass ψ A B := by
  unfold qBipartiteMatchMass
  exact Finset.sum_nonneg fun a _ =>
    ev_nonneg_of_psd ψ _ <| opTensor_nonneg (A.outcome_pos a) (B.outcome_pos a)

lemma qBipartiteConsDefect_le_one
    {Outcome : Type*} [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (hnorm : ψ.IsNormalized)
    (A B : SubMeas Outcome ι) :
    qBipartiteConsDefect ψ A B ≤ 1 := by
  unfold qBipartiteConsDefect
  have hmatch_nonneg : 0 ≤ qBipartiteMatchMass ψ A B := qBipartiteMatchMass_nonneg ψ A B
  have htotal_le : ev ψ (opTensor A.total B.total) ≤ 1 := by
    calc
      ev ψ (opTensor A.total B.total) ≤ ev ψ (leftTensor (ι₂ := ι) A.total) := by
            exact ev_mono ψ _ _ (opTensor_le_leftTensor A.total_nonneg B.total_le_one)
      _ ≤ 1 := by
            simpa [ev_one_of_isNormalized ψ hnorm] using
              ev_mono ψ _ _ (leftTensor_le_one (ι₂ := ι) A.total_le_one)
  have hinner : ev ψ (opTensor A.total B.total) - qBipartiteMatchMass ψ A B ≤ 1 := by
    linarith
  exact max_le_iff.mpr ⟨by positivity, hinner⟩

lemma bipartiteConsError_uniform_le_one
    {Question Outcome : Type*}
    [Fintype Question] [DecidableEq Question] [Nonempty Question]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (hnorm : ψ.IsNormalized)
    (A B : IdxSubMeas Question Outcome ι) :
    bipartiteConsError ψ (uniformDistribution Question) A B ≤ 1 := by
  unfold bipartiteConsError
  exact avgOver_uniform_le_const
    (fun q => qBipartiteConsDefect ψ (A q) (B q)) (1 : Error)
    (fun q => qBipartiteConsDefect_le_one ψ hnorm (A q) (B q))











end MIPStarRE.LDT.Pasting

end

/- Source helpers from MIPStarRE/LDT/Pasting/Bernoulli/Final.lean. -/
/-!
# Section 12 pasting: final pasting theorems

Final completeness and pasting theorems.
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]













-- The downstream completeness theorem elaborates the full `fromHToG` reduction facts.










/-- Trivial consistency conclusion when the target pasting error is at least `1`.

The consistency defect of two submeasurements against a normalized bipartite
state is always at most `1`; hence a scalar lower bound
`1 ≤ ldPastingInInductionError ...` is enough to produce the final conclusion
with a distinguished trivial measurement. -/
lemma ldPasting_of_one_le_error
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (family : IdxPolyFamily params ι)
    (k : ℕ)
    (herror :
      1 ≤ MainInductionStep.ldPastingInInductionError params k
        eps delta gamma kappa zeta) :
    ∃ H : Measurement (Polynomial params.next) ι,
      LdPastingConclusion params strategy family H eps delta gamma kappa zeta k := by
  let H : Measurement (Polynomial params.next) ι :=
    Measurement.trivialDistinguishedOutcome (fallbackInterpolatedPolynomial params)
  refine ⟨H, ?_⟩
  refine { pointConsistency := ?_ }
  exact ⟨le_trans
    (bipartiteConsError_uniform_le_one strategy.state strategy.isNormalized
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params.next H.toSubMeas))
    herror⟩

/-- Trivial consistency conclusion from the complementary scalar branches.

If `k` is positive, it suffices to show that the `ν` term in the pasting error
is at least `1`; if `k = 0`, the exponential term already gives the trivial
bound. -/
lemma ldPasting_of_one_le_nu_or_zero_k
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (family : IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (k : ℕ)
    (hnu :
      1 ≤ k →
        1 ≤ MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta) :
    ∃ H : Measurement (Polynomial params.next) ι,
      LdPastingConclusion params strategy family H eps delta gamma kappa zeta k := by
  exact ldPasting_of_one_le_error params strategy eps delta gamma kappa zeta family k (by
    have hkappa_nonneg := kappa_nonneg_of_complete params strategy family hcomplete
    by_cases hk_pos : 1 ≤ k
    · exact one_le_ldPastingError_of_one_le_nu params k eps delta gamma kappa zeta
        hkappa_nonneg (hnu hk_pos)
    · have hk_zero : k = 0 := by omega
      exact one_le_ldPastingError_of_k_eq_zero params k eps delta gamma kappa zeta
        hkappa_nonneg hk_zero)

/-- Complementary branch for `thm:ld-pasting` when `gamma > 1`.

Paper origin: `references/ldt-paper/ld-pasting.tex:52-55`, where this is one
of the large-error cases in which the final consistency bound is trivial.
This is one of the proved complementary cases for `thm:ld-pasting`. -/
theorem ldPastingLargeGammaBranch
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (_hself : family.StronglySelfConsistent strategy.state zeta)
    (_hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (_hk : 400 * params.m * params.d ≤ k)
    (hgamma : 1 < gamma) :
    ∃ H : Measurement (Polynomial params.next) ι,
      LdPastingConclusion params strategy family H eps delta gamma kappa zeta k := by
  exact ldPasting_of_one_le_nu_or_zero_k params strategy eps delta gamma kappa zeta
    family hcomplete k (fun hk_pos =>
      one_le_ldPastingNu_of_large_gamma params strategy eps delta gamma zeta
        hgood family hcons k hk_pos hgamma)

/-- Complementary branch for `thm:ld-pasting` when `zeta > 1`.

Paper origin: `references/ldt-paper/ld-pasting.tex:52-55`, where this is one
of the large-error cases in which the final consistency bound is trivial.
This is one of the proved complementary cases for `thm:ld-pasting`. -/
theorem ldPastingLargeZetaBranch
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (_hcons : family.ConsistentWithPoints strategy zeta)
    (_hself : family.StronglySelfConsistent strategy.state zeta)
    (_hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (_hk : 400 * params.m * params.d ≤ k)
    (hzeta : 1 < zeta) :
    ∃ H : Measurement (Polynomial params.next) ι,
      LdPastingConclusion params strategy family H eps delta gamma kappa zeta k := by
  exact ldPasting_of_one_le_nu_or_zero_k params strategy eps delta gamma kappa zeta
    family hcomplete k (fun hk_pos =>
      one_le_ldPastingNu_of_large_zeta params strategy eps delta gamma zeta
        hgood k hk_pos hzeta)

/-- Complementary branch for `thm:ld-pasting` when `d > q`.

Paper origin: `references/ldt-paper/ld-pasting.tex:52-55`, where this is the
large-error case `(d/q) ≥ 1`.  This is one of the proved complementary cases
for `thm:ld-pasting`. -/
theorem ldPastingLargeDegreeRatioBranch
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (_hself : family.StronglySelfConsistent strategy.state zeta)
    (_hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (_hk : 400 * params.m * params.d ≤ k)
    (hdq : params.q < params.d) :
    ∃ H : Measurement (Polynomial params.next) ι,
      LdPastingConclusion params strategy family H eps delta gamma kappa zeta k := by
  exact ldPasting_of_one_le_nu_or_zero_k params strategy eps delta gamma kappa zeta
    family hcomplete k (fun hk_pos =>
      one_le_ldPastingNu_of_large_degreeRatio params strategy eps delta gamma zeta
        hgood family hcons k hk_pos hdq)

/-- Complementary branch for `thm:ld-pasting` when `k = 0`.

This branch is a boundary case for the reduction to the nontrivial theorem,
whose proof assumes `1 ≤ k`.  The scalar calculation showing that the
exponential term gives the trivial bound is proved in `ScalarBounds.lean`. -/
theorem ldPastingZeroKBranch
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (_hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (_hcons : family.ConsistentWithPoints strategy zeta)
    (_hself : family.StronglySelfConsistent strategy.state zeta)
    (_hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (_hk : 400 * params.m * params.d ≤ k)
    (hk_zero : k = 0) :
    ∃ H : Measurement (Polynomial params.next) ι,
      LdPastingConclusion params strategy family H eps delta gamma kappa zeta k := by
  exact ldPasting_of_one_le_error params strategy eps delta gamma kappa zeta family k (by
    exact one_le_ldPastingError_of_k_eq_zero params k eps delta gamma kappa zeta
      (kappa_nonneg_of_complete params strategy family hcomplete) hk_zero)

/-- Degree-zero complementary branch for the unrestricted source theorem.

Paper origin: `references/ldt-paper/ld-pasting.tex:12-55`.  The paper's
large-error reduction names the cases
`eps, delta, gamma, zeta, d/q ≥ 1`; it does not explicitly add `0 < d` as a
hypothesis of `thm:ld-pasting`.  Thus the Lean theorem should not add `0 < d`
as an assumption of that cited theorem.

Issue #1622 recorded the need for a direct proof of this degree-zero branch; see
`docs/paper-gaps/issue-1622-ld-pasting-degree-zero.tex`.  The existing
nontrivial argument cannot simply be reused: its `hBConsistency` aggregation
passes from distinct sampled heights to independent sampled heights and absorbs
the resulting `k^2/q` loss through the displayed `(d/q)^(1/32)` term.  When
`d = 0`, that term is zero, so the branch requires a separate argument rather
than an additional hypothesis on `ldPasting`. -/
theorem ldPastingDegreeZeroBranch
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (_hself : family.StronglySelfConsistent strategy.state zeta)
    (_hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (_hk : 400 * params.m * params.d ≤ k)
    (hd_zero : params.d = 0)
    (_hk_pos : 1 ≤ k) :
    ∃ H : Measurement (Polynomial params.next) ι,
      LdPastingConclusion params strategy family H eps delta gamma kappa zeta k := by
  obtain ⟨H, _hHdef, hH⟩ :=
    degreeZeroPastedPointConsistency params strategy eps delta gamma kappa zeta
      hgood family hcomplete hcons hd_zero k
  exact ⟨H, { pointConsistency := hH }⟩

/-- Projection from the restricted nontrivial construction.

The restricted construction theorem `ldPastingNontrivial` proves the nontrivial
analytic regime for the canonical pasted measurement.  This auxiliary statement
records the projection from the restricted construction theorem to the conclusion
needed by the unrestricted theorem, without changing the statement of
`thm:ld-pasting`. -/
theorem ldPastingNontrivialPublicBranch
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hgamma_le : gamma ≤ 1)
    (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (hd : 0 < params.d)
    (family : IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hk_pos : 1 ≤ k)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ H : Measurement (Polynomial params.next) ι,
      LdPastingConclusion params strategy family H eps delta gamma kappa zeta k := by
  obtain ⟨H, _hHdef, hH⟩ :=
    ldPastingNontrivial params strategy eps delta gamma kappa zeta
      hgood hgamma_le hzeta_le hdq_le hd
      family hcomplete hcons hself hbound k hk_pos hk
  exact ⟨H, hH⟩



end MIPStarRE.LDT.Pasting

end

end LIDT

open LIDT
/-!
# Section 12 pasting: final pasting theorems

Final completeness and pasting theorems.
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]













-- The downstream completeness theorem elaborates the full `fromHToG` reduction facts.

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters)
    [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (strategy : _root_.LIDT.MIPStarRE.LDT.SymStrat params.next ι)
    (eps delta gamma kappa zeta : _root_.LIDT.MIPStarRE.LDT.Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ H : _root_.LIDT.MIPStarRE.LDT.Measurement (_root_.LIDT.MIPStarRE.LDT.Polynomial params.next) ι,
      _root_.LIDT.MIPStarRE.LDT.Pasting.LdPastingConclusion params strategy family H eps delta gamma kappa zeta k := by
  by_cases hgamma_le : gamma ≤ 1
  · by_cases hzeta_le : zeta ≤ 1
    · by_cases hdq_le : params.d ≤ params.q
      · by_cases hd : 0 < params.d
        · by_cases hk_pos : 1 ≤ k
          · exact _root_.LIDT.MIPStarRE.LDT.Pasting.ldPastingNontrivialPublicBranch params strategy eps delta gamma kappa zeta
              hgood hgamma_le hzeta_le hdq_le hd family hcomplete hcons hself hbound
              k hk_pos hk
          · have hk_zero : k = 0 := by omega
            exact _root_.LIDT.MIPStarRE.LDT.Pasting.ldPastingZeroKBranch params strategy eps delta gamma kappa zeta
              hgood family hcomplete hcons hself hbound k hk hk_zero
        · have hd_zero : params.d = 0 := Nat.eq_zero_of_not_pos hd
          by_cases hk_pos : 1 ≤ k
          · exact _root_.LIDT.MIPStarRE.LDT.Pasting.ldPastingDegreeZeroBranch params strategy eps delta gamma kappa zeta
              hgood family hcomplete hcons hself hbound k hk hd_zero hk_pos
          · have hk_zero : k = 0 := by omega
            exact _root_.LIDT.MIPStarRE.LDT.Pasting.ldPastingZeroKBranch params strategy eps delta gamma kappa zeta
              hgood family hcomplete hcons hself hbound k hk hk_zero
      · have hdq : params.q < params.d := by omega
        exact _root_.LIDT.MIPStarRE.LDT.Pasting.ldPastingLargeDegreeRatioBranch params strategy eps delta gamma kappa zeta
          hgood family hcomplete hcons hself hbound k hk hdq
    · have hzeta : 1 < zeta := lt_of_not_ge hzeta_le
      exact _root_.LIDT.MIPStarRE.LDT.Pasting.ldPastingLargeZetaBranch params strategy eps delta gamma kappa zeta
        hgood family hcomplete hcons hself hbound k hk hzeta
  · have hgamma : 1 < gamma := lt_of_not_ge hgamma_le
    exact _root_.LIDT.MIPStarRE.LDT.Pasting.ldPastingLargeGammaBranch params strategy eps delta gamma kappa zeta
      hgood family hcomplete hcons hself hbound k hk hgamma
