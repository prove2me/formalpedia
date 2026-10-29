-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.degreeZeroPastedPointConsistency
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:30:45.707781+00:00
-- url     : https://prove2.me/submissions/741de64a-9ec6-4c5c-9a84-1929cc92ed85

-- Generated proof for MIPStarRE.LDT.Pasting.degreeZeroPastedPointConsistency.
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
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.RingTheory.MvPolynomial.Basic
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_hAConsistency_sqrt_bound_of_pos
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_ldGbcon_of_axis_self
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_pointVerticalLineSdd_of_axis_self
import Theorems.Thm_LIDT_MIPStarRE_LDT_Preliminaries_evaluateAt_completeAtOutcome
import Theorems.Thm_LIDT_MIPStarRE_LDT_Preliminaries_qBipartiteConsDefect_completeAtOutcome_right_le
import Theorems.Thm_LIDT_MIPStarRE_LDT_Preliminaries_triangleSub_right

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

/- Source helpers from MIPStarRE/LDT/Basic/LinePolynomials.lean. -/
/-!
# One-variable line polynomials for the low individual degree test

Polynomial answer types attached to axis-parallel and diagonal lines.

## References

- `references/ldt-paper/test_definition.tex`
- `blueprint/src/chapter/ch02_test.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT











namespace AxisLinePolynomial





/-- A degree-zero axis-line answer is a constant univariate polynomial.

Lean-only helper for the degree-zero branch of `thm:ld-pasting`; the source
context is `references/ldt-paper/ld-pasting.tex:12-55`, where the boundary
case `d = 0` must be handled without adding `0 < d` to the theorem. -/
theorem eq_C_coeff_zero_of_degree_zero {params : Parameters} [FieldModel params.q]
    (f : AxisLinePolynomial params) (hd : params.d = 0) :
    f.poly = _root_.Polynomial.C (f.poly.coeff 0) := by
  exact _root_.Polynomial.eq_C_of_natDegree_eq_zero
    (Nat.eq_zero_of_le_zero (f.degreeBounded.trans (by simp [hd])))

/-- A degree-zero axis-line answer has the same value at all line parameters.

Lean-only helper for the degree-zero branch of `thm:ld-pasting`; this is the
vertical-line analogue of `Polynomial.apply_eq_apply_of_degree_zero`. -/
theorem apply_eq_apply_of_degree_zero {params : Parameters} [FieldModel params.q]
    (f : AxisLinePolynomial params) (hd : params.d = 0) (t s : Fq params) :
    f t = f s := by
  unfold AxisLinePolynomial.toFun evalLinePolynomialModel
  rw [eq_C_coeff_zero_of_degree_zero f hd]
  simp





























end AxisLinePolynomial





namespace DiagonalLinePolynomial































end DiagonalLinePolynomial

/-! ## Paper-level diagonal-line answers -/



namespace DiagonalLineAnswer























end DiagonalLineAnswer

namespace DiagonalLinePolynomial









end DiagonalLinePolynomial

end MIPStarRE.LDT

end

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

/-- The ratio `d / q` is nonnegative in the error scalar field. -/
lemma ldPasting_degreeRatio_nonneg
    (params : Parameters)
    [FieldModel params.q] :
    0 ≤ ((params.d : Error) / (params.q : Error)) := by
  exact div_nonneg (by exact_mod_cast Nat.zero_le params.d) (le_of_lt params.q_cast_pos)







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

lemma qBipartiteSSCDefect_le_one
    {Outcome : Type*} [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (hnorm : ψ.IsNormalized)
    (A : SubMeas Outcome ι) :
    qBipartiteSSCDefect ψ A ≤ 1 := by
  unfold qBipartiteSSCDefect
  have hoverlap_nonneg : 0 ≤ ∑ a : Outcome, ev ψ (opTensor (A.outcome a) (A.outcome a)) := by
    exact Finset.sum_nonneg fun a _ =>
      ev_nonneg_of_psd ψ _ <| opTensor_nonneg (A.outcome_pos a) (A.outcome_pos a)
  have htotal_le : ev ψ (leftTensor (ι₂ := ι) A.total) ≤ 1 := by
    simpa [ev_one_of_isNormalized ψ hnorm] using
      ev_mono ψ _ _ (leftTensor_le_one (ι₂ := ι) A.total_le_one)
  have hinner : ev ψ (leftTensor (ι₂ := ι) A.total) -
      ∑ a : Outcome, ev ψ (opTensor (A.outcome a) (A.outcome a)) ≤ 1 := by
    linarith
  exact max_le_iff.mpr ⟨by positivity, hinner⟩

lemma bipartiteSSCError_uniform_le_one
    {Question Outcome : Type*}
    [Fintype Question] [DecidableEq Question] [Nonempty Question]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (hnorm : ψ.IsNormalized)
    (A : IdxSubMeas Question Outcome ι) :
    bipartiteSSCError ψ (uniformDistribution Question) A ≤ 1 := by
  unfold bipartiteSSCError
  exact avgOver_uniform_le_const
    (fun q => qBipartiteSSCDefect ψ (A q)) (1 : Error)
    (fun q => qBipartiteSSCDefect_le_one ψ hnorm (A q))







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





lemma max_zero_add_le
    (a t : Error) (ha : 0 ≤ a) :
    max 0 (a + t) ≤ a + max 0 t := by
  by_cases ht : 0 ≤ t
  · rw [max_eq_right (add_nonneg ha ht), max_eq_right ht]
  · have ht' : t ≤ 0 := le_of_not_ge ht
    by_cases hat : 0 ≤ a + t
    · rw [max_eq_right hat, max_eq_left ht']
      linarith
    · have hat' : a + t ≤ 0 := le_of_not_ge hat
      rw [max_eq_left hat', max_eq_left ht']
      linarith

lemma max_zero_mul_add_le
    (w a t : Error)
    (hw : 0 ≤ w) :
    max 0 (w * a + t) ≤ w * max 0 a + max 0 t := by
  have hwa : w * a ≤ w * max 0 a := by
    exact mul_le_mul_of_nonneg_left (le_max_right 0 a) hw
  calc
    max 0 (w * a + t) ≤ max 0 (w * max 0 a + t) := by
      have hadd : w * a + t ≤ w * max 0 a + t := by linarith
      exact max_le_max le_rfl hadd
    _ ≤ w * max 0 a + max 0 t := by
      exact max_zero_add_le (w * max 0 a) t (mul_nonneg hw (by positivity))

lemma max_zero_avgOver_le_avgOver_max_zero
    {α : Type*}
    (𝒟 : Distribution α)
    (f : α → Error) :
    max 0 (avgOver 𝒟 f) ≤ avgOver 𝒟 (fun a => max 0 (f a)) := by
  classical
  unfold avgOver
  induction 𝒟.support using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      calc
        max 0 (𝒟.weight a * f a + ∑ x ∈ s, 𝒟.weight x * f x)
          ≤ 𝒟.weight a * max 0 (f a) + max 0 (∑ x ∈ s, 𝒟.weight x * f x) := by
              exact max_zero_mul_add_le (𝒟.weight a) (f a)
                (∑ x ∈ s, 𝒟.weight x * f x) (𝒟.nonnegative a)
        _ ≤ 𝒟.weight a * max 0 (f a) + ∑ x ∈ s, 𝒟.weight x * max 0 (f x) := by
              simpa [add_comm, add_left_comm, add_assoc] using
                add_le_add_right ih (𝒟.weight a * max 0 (f a))

lemma qBipartiteMatchMass_averageIdxSubMeas_left
    {Question Outcome : Type*}
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι)
    (B : SubMeas Outcome ι)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1) :
    qBipartiteMatchMass ψ (averageIdxSubMeas 𝒟 A h𝒟) B =
      avgOver 𝒟 (fun q => qBipartiteMatchMass ψ (A q) B) := by
  classical
  unfold qBipartiteMatchMass averageIdxSubMeas
  calc
    ∑ a,
        ev ψ
          (opTensor (averageOperatorOverDistribution 𝒟 (fun q => (A q).outcome a))
            (B.outcome a))
      = ∑ a, avgOver 𝒟
          (fun q => ev ψ (opTensor ((A q).outcome a) (B.outcome a))) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              exact ev_opTensor_averageOperatorOverDistribution_left ψ 𝒟
                (fun q => (A q).outcome a) (B.outcome a)
    _ = avgOver 𝒟
          (fun q => ∑ a, ev ψ (opTensor ((A q).outcome a) (B.outcome a))) := by
          rw [← avgOver_sum]
    _ = avgOver 𝒟 (fun q => qBipartiteMatchMass ψ (A q) B) := by
          simp [avgOver, qBipartiteMatchMass]

lemma ev_opTensor_total_averageIdxSubMeas_left
    {Question Outcome : Type*}
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι)
    (B : SubMeas Outcome ι)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1) :
    ev ψ (opTensor (averageIdxSubMeas 𝒟 A h𝒟).total B.total) =
      avgOver 𝒟 (fun q => ev ψ (opTensor (A q).total B.total)) := by
  classical
  unfold averageIdxSubMeas
  change ev ψ (opTensor (averageOperatorOverDistribution 𝒟 (fun q => (A q).total)) B.total) = _
  exact ev_opTensor_averageOperatorOverDistribution_left ψ 𝒟 (fun q => (A q).total) B.total

lemma qBipartiteConsDefect_averageIdxSubMeas_left_le
    {Question Outcome : Type*}
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι)
    (B : SubMeas Outcome ι)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1) :
    qBipartiteConsDefect ψ (averageIdxSubMeas 𝒟 A h𝒟) B ≤
      avgOver 𝒟 (fun q => qBipartiteConsDefect ψ (A q) B) := by
  have htotal := ev_opTensor_total_averageIdxSubMeas_left ψ 𝒟 A B h𝒟
  have hmatch := qBipartiteMatchMass_averageIdxSubMeas_left ψ 𝒟 A B h𝒟
  rw [qBipartiteConsDefect, htotal, hmatch]
  rw [← avgOver_sub]
  exact le_trans
    (max_zero_avgOver_le_avgOver_max_zero 𝒟
      (fun q => ev ψ (opTensor (A q).total B.total) - qBipartiteMatchMass ψ (A q) B)) <| by
        refine avgOver_mono 𝒟 _ _ ?_
        intro q
        simp [qBipartiteConsDefect]

end MIPStarRE.LDT.Pasting

end

/- Source helpers from MIPStarRE/LDT/Pasting/ComparisonLemmas/LineInterpolation/BadLine.lean. -/
/-!
# Line interpolation: bad-line event

Definitions and lemmas for `tupleInterpolatedVerticalLine` and mismatch
extraction in the line-interpolation argument.

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



lemma evaluateAt_averageIdxSubMeas
    (params : Parameters) [FieldModel params.q]
    {Question : Type*}
    (u : Point params)
    (𝒟 : Distribution Question)
    (A : IdxSubMeas Question (Polynomial params) ι)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1) :
    evaluateAt params u (averageIdxSubMeas 𝒟 A h𝒟) =
      averageIdxSubMeas 𝒟 (fun q => evaluateAt params u (A q)) h𝒟 := by
  classical
  refine SubMeas.ext ?_ ?_
  · intro a
    simp [evaluateAt, postprocess, averageIdxSubMeas, averageOperatorOverDistribution,
      Finset.sum_filter, Finset.sum_comm, Finset.smul_sum]
  · simp [evaluateAt, postprocess, averageIdxSubMeas, averageOperatorOverDistribution]





end MIPStarRE.LDT.Pasting

end

/- Source helpers from MIPStarRE/LDT/Pasting/Core/LdGbcon.lean. -/
/-!
# Section 12 pasting: vertical-line consistency transfer

The `ldGbcon` transfer compares the slice family `G^x` with the vertical-line
answers `B^u`.  It combines the conditioned axis-parallel consistency estimate
with the point-to-vertical-line state-dependent-distance bound.
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]











/-- Named submeasurement-family form of `pointVerticalLineSdd_of_axis_self`.

The proof above constructs the vertical-line measurement as a complete
measurement-valued family.  The degree-zero estimates use only its underlying
submeasurement family, namely `liftedVerticalLineAnswerFamily`. -/
theorem pointVerticalLineSdd_liftedVerticalLine_of_axis_self
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta : Error)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself : strategy.selfConsistencyFailureProbability ≤ delta) :
    SDDRel strategy.state
      (uniformDistribution (Point params.next))
      (IdxSubMeas.liftRight (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
      (IdxSubMeas.liftRight (liftedVerticalLineAnswerFamily params strategy))
      (8 * (params.m : Error) * eps + 4 * delta) := by
  change SDDRel strategy.state
    (uniformDistribution (Point params.next))
    (IdxSubMeas.liftRight (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
    (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas (ldGbconVerticalLineMeasurement params strategy)))
    (8 * (params.m : Error) * eps + 4 * delta)
  exact pointVerticalLineSdd_of_axis_self params strategy eps delta haxis hself







/-- Named-family form of `lem:ld-gbcon`.

This is the same consistency transfer as `ldGbcon`, restated with the two
families used in the degree-zero branch of `thm:ld-pasting`: the evaluated slice
family `family.evaluatedAtNextPoint` and the lifted vertical-line family
`liftedVerticalLineAnswerFamily`.  In the degree-zero branch, these are the two
families whose pointwise invariance properties must be combined to control
height dependence. -/
theorem ldGbcon_liftedVerticalLine_of_axis_self
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta zeta : Error)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself : strategy.selfConsistencyFailureProbability ≤ delta)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta) :
    ConsRel strategy.state
      (uniformDistribution (Point params.next))
      family.evaluatedAtNextPoint
      (liftedVerticalLineAnswerFamily params strategy)
      (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta)) := by
  change ConsRel strategy.state
    (uniformDistribution (Point params.next))
    (evaluateFiberFamilyAtNextPoint params (IdxProjSubMeas.toIdxSubMeas family.meas))
    (fun u =>
      postprocess
        (verticalLineMeasurementFamily params strategy (truncatePoint params u))
        (fun f => f (pointHeight params u)))
    (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta))
  exact ldGbcon_of_axis_self params strategy eps delta zeta haxis hself family hcons

/-- Named-family form of `lem:ld-gbcon`. -/
theorem ldGbcon_liftedVerticalLine
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta) :
    ConsRel strategy.state
      (uniformDistribution (Point params.next))
      family.evaluatedAtNextPoint
      (liftedVerticalLineAnswerFamily params strategy)
      (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta)) := by
  exact ldGbcon_liftedVerticalLine_of_axis_self params strategy eps delta zeta
    hgood.axisParallelTest hgood.selfConsistencyTest family hcons

end MIPStarRE.LDT.Pasting

end

/- Source helpers from MIPStarRE/LDT/Test/StrategyPolynomialFamilies.lean. -/
/-!
# Polynomial-family interfaces for the low individual degree test

Packaged slice-indexed polynomial-family interfaces extracted from
`MIPStarRE.LDT.Test.Strategy`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT

/-! ### Polynomial-family interfaces -/



-- NOTE: no global `Inhabited` instance for `IdxPolyFamily`; without an actual
-- slice family, any default would be a degenerate zero-family placeholder.

namespace IdxPolyFamily



































/-- A family point-consistency witness forces the displayed point-consistency
error parameter `ζ` to be nonnegative. -/
theorem zeta_nonneg_of_consistentWithPoints {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {zeta : Error}
    (hcons : family.ConsistentWithPoints strategy zeta) :
    0 ≤ zeta := by
  exact le_trans
    (bipartiteConsError_nonneg strategy.state
      (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      family.evaluatedAtNextPoint)
    hcons.pointConsistency.offDiagonalBound





namespace SliceBoundednessInput







end SliceBoundednessInput

end IdxPolyFamily

end MIPStarRE.LDT

end

/- Source helpers from MIPStarRE/LDT/Pasting/Sandwich/PastedFamilies.lean. -/
/-!
# Section 12 — Sandwich constructions: pasted families

Pasted interpolation families, recurrence weights, and final operator families.
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]















/-- Evaluating the averaged appended-slice submeasurement at a next-level point
is the same as evaluating the averaged slice family at the truncated point.

This is the first formal step in the degree-zero branch of `thm:ld-pasting`;
the later consistency rectangle compares this averaged slice construction with
the point measurement. -/
theorem evaluateAt_averagedSliceAppendedSubMeas
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (u : Point params.next) :
    evaluateAt params.next u (averagedSliceAppendedSubMeas params family) =
      evaluateAt params (truncatePoint params u) family.averagedSubMeas := by
  have hpoint :
      appendPoint params (truncatePoint params u) (pointHeight params u) = u :=
    (CommutativityPoints.pointNextEquiv params).left_inv u
  rw [← hpoint]
  simp [averagedSliceAppendedSubMeas,
    evaluateAt_postprocess_appendAtHeight_appendPoint params
      family.averagedSubMeas zeroCoord (truncatePoint params u) (pointHeight params u)]







/-- In degree zero, the lifted vertical-line answer family is independent of
the height coordinate once the old point coordinates are fixed.

Lean-only helper for the degree-zero branch of `thm:ld-pasting`; it formalizes
the fact that a vertical line answer of degree zero is constant in the line
parameter.  The source context is `references/ldt-paper/ld-pasting.tex:12-55`. -/
theorem liftedVerticalLineAnswerFamily_eq_of_same_truncate_degree_zero
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (hd : params.d = 0)
    {u v : Point params.next} (hbase : truncatePoint params u = truncatePoint params v) :
    liftedVerticalLineAnswerFamily params strategy u =
      liftedVerticalLineAnswerFamily params strategy v := by
  unfold liftedVerticalLineAnswerFamily
  rw [hbase]
  congr
  funext f
  have hd_next : params.next.d = 0 := by
    simpa [Parameters.next] using hd
  exact AxisLinePolynomial.apply_eq_apply_of_degree_zero f hd_next
    (pointHeight params u) (pointHeight params v)























end MIPStarRE.LDT.Pasting

end

/- Source helpers from MIPStarRE/LDT/Pasting/Bernoulli/DegreeZero.lean. -/
/-!
# Section 12 pasting: degree-zero branch

Auxiliary constructions for the `d = 0` complementary branch of
`thm:ld-pasting`.

## References

- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Evaluating the degree-zero appended-slice candidate is the height average of
the original evaluated slice family at the same old point. -/
private theorem polynomialEvaluation_averagedSliceAppendedSubMeas_eq_average
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (u : Point params.next) :
    polynomialEvaluationFamily params.next
        (averagedSliceAppendedSubMeas params family) u =
      averageIdxSubMeas (uniformDistribution (Fq params))
        (fun x =>
          family.evaluatedAtNextPoint
            (appendPoint params (truncatePoint params u) x))
        (uniformDistribution_weight_sum_le_one (Fq params)) := by
  calc
    polynomialEvaluationFamily params.next
        (averagedSliceAppendedSubMeas params family) u
        = evaluateAt params.next u (averagedSliceAppendedSubMeas params family) := rfl
    _ = evaluateAt params (truncatePoint params u) family.averagedSubMeas := by
        exact evaluateAt_averagedSliceAppendedSubMeas params family u
    _ = averageIdxSubMeas (uniformDistribution (Fq params))
          (fun x => evaluateAt params (truncatePoint params u)
            ((family.meas x).toSubMeas))
          (uniformDistribution_weight_sum_le_one (Fq params)) := by
        exact evaluateAt_averageIdxSubMeas params (truncatePoint params u)
          (uniformDistribution (Fq params))
          (fun x => (family.meas x).toSubMeas)
          (uniformDistribution_weight_sum_le_one (Fq params))
    _ = averageIdxSubMeas (uniformDistribution (Fq params))
          (fun x =>
            family.evaluatedAtNextPoint
              (appendPoint params (truncatePoint params u) x))
          (uniformDistribution_weight_sum_le_one (Fq params)) := by
        congr
        funext x
        simp [IdxPolyFamily.evaluatedAtNextPoint, truncatePoint_appendPoint,
          pointHeight_appendPoint]

/-- The point-consistency hypothesis may be truncated at the trivial unit bound. -/
private theorem consistentWithPoints_min_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (zeta : Error)
    (hcons : family.ConsistentWithPoints strategy zeta) :
    family.ConsistentWithPoints strategy (min zeta 1) := by
  refine ⟨?_⟩
  refine ⟨?_⟩
  exact le_min hcons.pointConsistency.offDiagonalBound
    (bipartiteConsError_uniform_le_one strategy.state strategy.isNormalized
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      family.evaluatedAtNextPoint)

/-- Scalar absorption for the degree-zero submeasurement consistency error. -/
private theorem degreeZero_submeas_error_le_two_nu
    (params : Parameters) [FieldModel params.q]
    (eps delta gamma zeta : Error) (k : ℕ)
    (hk_pos : 1 ≤ k)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta) :
    min zeta 1 +
        2 * Real.sqrt (8 * (params.m : Error) * min eps 1 + 4 * min delta 1) ≤
      2 * MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta := by
  let C : Error := ((k : Error) ^ (2 : ℕ)) * (params.m : Error)
  let epsTerm : Error := Real.rpow eps (1 / (32 : Error))
  let deltaTerm : Error := Real.rpow delta (1 / (32 : Error))
  let gammaTerm : Error := Real.rpow gamma (1 / (32 : Error))
  let zetaTerm : Error := Real.rpow zeta (1 / (32 : Error))
  let degreeTerm : Error :=
    Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))
  let S : Error := epsTerm + deltaTerm + gammaTerm + zetaTerm + degreeTerm
  have hC_one : (1 : Error) ≤ C := by
    have hkE_one : (1 : Error) ≤ (k : Error) := by exact_mod_cast hk_pos
    have hmE_one : (1 : Error) ≤ (params.m : Error) := by
      exact_mod_cast (Nat.succ_le_of_lt params.hm)
    dsimp [C]
    nlinarith [sq_nonneg (k : Error)]
  have hC_nonneg : 0 ≤ C := le_trans zero_le_one hC_one
  have hepsTerm_nonneg : 0 ≤ epsTerm := by
    dsimp [epsTerm]
    exact Real.rpow_nonneg heps_nonneg _
  have hdeltaTerm_nonneg : 0 ≤ deltaTerm := by
    dsimp [deltaTerm]
    exact Real.rpow_nonneg hdelta_nonneg _
  have hgammaTerm_nonneg : 0 ≤ gammaTerm := by
    dsimp [gammaTerm]
    exact Real.rpow_nonneg hgamma_nonneg _
  have hzetaTerm_nonneg : 0 ≤ zetaTerm := by
    dsimp [zetaTerm]
    exact Real.rpow_nonneg hzeta_nonneg _
  have hdegreeTerm_nonneg : 0 ≤ degreeTerm := by
    dsimp [degreeTerm]
    exact Real.rpow_nonneg (ldPasting_degreeRatio_nonneg params) _
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    nlinarith
  have hzeta_min_le_C : min zeta 1 ≤ C * zetaTerm := by
    have hmin_nonneg : 0 ≤ min zeta 1 := by positivity
    have hmin_le_one : min zeta 1 ≤ 1 := min_le_right _ _
    have hzeta_min_le : min zeta 1 ≤ zetaTerm := by
      calc
        min zeta 1 ≤ Real.rpow (min zeta 1) (1 / (32 : Error)) := by
            simpa [Real.rpow_one] using
              (Real.rpow_le_rpow_of_exponent_ge' hmin_nonneg hmin_le_one
                (show 0 ≤ (1 / (32 : Error)) by norm_num)
                (show 1 / (32 : Error) ≤ (1 : Error) by norm_num))
        _ ≤ zetaTerm := by
            dsimp [zetaTerm]
            exact Real.rpow_le_rpow hmin_nonneg (min_le_left _ _) (by positivity)
    calc
      min zeta 1 ≤ zetaTerm := hzeta_min_le
      _ = (1 : Error) * zetaTerm := by ring
      _ ≤ C * zetaTerm := by
          exact mul_le_mul_of_nonneg_right hC_one hzetaTerm_nonneg
  have hsqrt_le_CS :
      Real.sqrt (8 * (params.m : Error) * min eps 1 + 4 * min delta 1) ≤ 3 * C * S := by
    calc
      Real.sqrt (8 * (params.m : Error) * min eps 1 + 4 * min delta 1)
          ≤ 3 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) *
              (Real.rpow eps (1 / (32 : Error)) + Real.rpow delta (1 / (32 : Error))) :=
            hAConsistency_sqrt_bound_of_pos params eps delta k hk_pos
              heps_nonneg hdelta_nonneg
      _ = 3 * C * (epsTerm + deltaTerm) := by ring
      _ ≤ 3 * C * S := by
          have hsum_le : epsTerm + deltaTerm ≤ S := by
            dsimp [S]
            nlinarith
          exact mul_le_mul_of_nonneg_left hsum_le (by positivity)
  calc
    min zeta 1 +
        2 * Real.sqrt (8 * (params.m : Error) * min eps 1 + 4 * min delta 1)
      ≤ C * zetaTerm + 2 * (3 * C * S) := by
          exact add_le_add hzeta_min_le_C
            (mul_le_mul_of_nonneg_left hsqrt_le_CS (by norm_num))
    _ ≤ 7 * C * S := by
          have hzeta_le_S : zetaTerm ≤ S := by
            dsimp [S]
            nlinarith
          have hCzeta_le_CS : C * zetaTerm ≤ C * S := by
            exact mul_le_mul_of_nonneg_left hzeta_le_S hC_nonneg
          nlinarith
    _ ≤ 200 * C * S := by
          have hCS_nonneg : 0 ≤ C * S := mul_nonneg hC_nonneg hS_nonneg
          nlinarith
    _ = 2 * MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta := by
          simp [MainInductionStep.ldPastingInInductionNu, C, S, epsTerm, deltaTerm,
            gammaTerm, zetaTerm, degreeTerm]
          ring

/-- The averaged degree-zero pasted submeasurement is consistent with the lifted
vertical-line answers. -/
private theorem degreeZero_averagedSlice_liftedVerticalLineConsistency
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hd_zero : params.d = 0) :
    ConsRel strategy.state (uniformDistribution (Point params.next))
      (polynomialEvaluationFamily params.next
        (averagedSliceAppendedSubMeas params family))
      (liftedVerticalLineAnswerFamily params strategy)
      (min zeta 1 +
        Real.sqrt (8 * (params.m : Error) * min eps 1 + 4 * min delta 1)) := by
  let eps' : Error := min eps 1
  let delta' : Error := min delta 1
  let zeta' : Error := min zeta 1
  have haxis_le_one : strategy.axisParallelFailureProbability ≤ 1 := by
    simpa [SymStrat.axisParallelFailureProbability] using
      bipartiteConsError_uniform_le_one strategy.state strategy.isNormalized
        (axisParallelPointAnswerFamily strategy)
        (axisParallelLineAnswerFamily strategy)
  have hself_le_one : strategy.selfConsistencyFailureProbability ≤ 1 := by
    simpa [SymStrat.selfConsistencyFailureProbability] using
      bipartiteSSCError_uniform_le_one strategy.state strategy.isNormalized
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
  have hgood_small : strategy.IsGood eps' delta' gamma := by
    refine ⟨?_, ?_, hgood.diagonalLineTest⟩
    · exact le_min hgood.axisParallelTest haxis_le_one
    · exact le_min hgood.selfConsistencyTest hself_le_one
  have hcons_small : family.ConsistentWithPoints strategy zeta' := by
    simpa [zeta'] using consistentWithPoints_min_one params strategy family zeta hcons
  have hgb := ldGbcon_liftedVerticalLine params strategy eps' delta' gamma zeta'
    hgood_small family hcons_small
  let F : Point params → Fq params → Error := fun u x =>
    qBipartiteConsDefect strategy.state
      (family.evaluatedAtNextPoint (appendPoint params u x))
      (liftedVerticalLineAnswerFamily params strategy (appendPoint params u x))
  have haverage_to_gb :
      avgOver (uniformDistribution (Point params.next))
          (fun u => avgOver (uniformDistribution (Fq params))
            (fun x => F (truncatePoint params u) x)) =
        bipartiteConsError strategy.state (uniformDistribution (Point params.next))
          family.evaluatedAtNextPoint
          (liftedVerticalLineAnswerFamily params strategy) := by
    calc
      avgOver (uniformDistribution (Point params.next))
          (fun u => avgOver (uniformDistribution (Fq params))
            (fun x => F (truncatePoint params u) x))
        = avgOver (uniformDistribution (Fq params))
            (fun _ => avgOver (uniformDistribution (Point params))
              (fun u => avgOver (uniformDistribution (Fq params)) (fun x => F u x))) := by
            simpa [truncatePoint_appendPoint] using
              CommutativityPoints.avgOver_uniform_pointNext_decompose params
                (fun u => avgOver (uniformDistribution (Fq params))
                  (fun x => F (truncatePoint params u) x))
      _ = avgOver (uniformDistribution (Point params))
            (fun u => avgOver (uniformDistribution (Fq params)) (fun x => F u x)) := by
            simpa using avgOver_uniform_const (α := Fq params)
              (avgOver (uniformDistribution (Point params))
                (fun u => avgOver (uniformDistribution (Fq params)) (fun x => F u x)))
      _ = avgOver (uniformDistribution (Fq params))
            (fun x => avgOver (uniformDistribution (Point params)) (fun u => F u x)) := by
            exact avgOver_uniform_comm (fun u x => F u x)
      _ = avgOver (uniformDistribution (Point params.next))
            (fun v => F (truncatePoint params v) (pointHeight params v)) := by
            simpa [truncatePoint_appendPoint, pointHeight_appendPoint] using
              (CommutativityPoints.avgOver_uniform_pointNext_decompose params
                (fun v => F (truncatePoint params v) (pointHeight params v))).symm
      _ = bipartiteConsError strategy.state (uniformDistribution (Point params.next))
          family.evaluatedAtNextPoint
          (liftedVerticalLineAnswerFamily params strategy) := by
            unfold bipartiteConsError
            apply avgOver_congr
            intro v
            have happend :
                appendPoint params (truncatePoint params v) (pointHeight params v) = v := by
              exact (CommutativityPoints.pointNextEquiv params).left_inv v
            simp [F, happend]
  constructor
  unfold bipartiteConsError
  calc
    avgOver (uniformDistribution (Point params.next))
        (fun u => qBipartiteConsDefect strategy.state
          (polynomialEvaluationFamily params.next
            (averagedSliceAppendedSubMeas params family) u)
          (liftedVerticalLineAnswerFamily params strategy u))
      ≤ avgOver (uniformDistribution (Point params.next))
          (fun u => avgOver (uniformDistribution (Fq params)) (fun x =>
            qBipartiteConsDefect strategy.state
              (family.evaluatedAtNextPoint (appendPoint params (truncatePoint params u) x))
              (liftedVerticalLineAnswerFamily params strategy u))) := by
          apply avgOver_mono
          intro u
          rw [polynomialEvaluation_averagedSliceAppendedSubMeas_eq_average params family u]
          exact qBipartiteConsDefect_averageIdxSubMeas_left_le strategy.state
            (uniformDistribution (Fq params))
            (fun x => family.evaluatedAtNextPoint
              (appendPoint params (truncatePoint params u) x))
            (liftedVerticalLineAnswerFamily params strategy u)
            (uniformDistribution_weight_sum_le_one (Fq params))
    _ = avgOver (uniformDistribution (Point params.next))
          (fun u => avgOver (uniformDistribution (Fq params))
            (fun x => F (truncatePoint params u) x)) := by
          apply avgOver_congr
          intro u
          apply avgOver_congr
          intro x
          have hline :
              liftedVerticalLineAnswerFamily params strategy
                  (appendPoint params (truncatePoint params u) x) =
                liftedVerticalLineAnswerFamily params strategy u := by
            exact liftedVerticalLineAnswerFamily_eq_of_same_truncate_degree_zero
              params strategy hd_zero (by simp)
          simp [F, hline]
    _ = bipartiteConsError strategy.state (uniformDistribution (Point params.next))
          family.evaluatedAtNextPoint
          (liftedVerticalLineAnswerFamily params strategy) := haverage_to_gb
    _ ≤ zeta' + Real.sqrt (8 * (params.m : Error) * eps' + 4 * delta') :=
          hgb.offDiagonalBound
    _ = min zeta 1 +
        Real.sqrt (8 * (params.m : Error) * min eps 1 + 4 * min delta 1) := by
          simp [eps', delta', zeta']

/-- The averaged degree-zero pasted submeasurement is point-consistent before
completion. -/
private theorem degreeZero_averagedSlice_pointConsistency
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hd_zero : params.d = 0) :
    ConsRel strategy.state (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params.next
        (averagedSliceAppendedSubMeas params family))
      (min zeta 1 +
        2 * Real.sqrt (8 * (params.m : Error) * min eps 1 + 4 * min delta 1)) := by
  let eps' : Error := min eps 1
  let delta' : Error := min delta 1
  let lineMeas : IdxMeas (Point params.next) (Fq params.next) ι := fun u =>
    { toSubMeas := liftedVerticalLineAnswerFamily params strategy u
      total_eq_one :=
        (strategy.axisParallelMeasurement
          { base := appendPoint params (truncatePoint params u) zeroCoord
            direction := lastCoord params }).total_eq_one }
  let pointMeas : IdxMeas (Point params.next) (Fq params.next) ι :=
    fun u => (strategy.pointMeasurement u).toMeasurement
  have hline :
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (polynomialEvaluationFamily params.next
          (averagedSliceAppendedSubMeas params family))
        (IdxMeas.toIdxSubMeas lineMeas)
        (min zeta 1 + Real.sqrt (8 * (params.m : Error) * eps' + 4 * delta')) := by
    have hline_eq :
        IdxMeas.toIdxSubMeas lineMeas =
          liftedVerticalLineAnswerFamily params strategy := by
      funext u
      rfl
    rw [hline_eq]
    simpa [eps', delta'] using
      degreeZero_averagedSlice_liftedVerticalLineConsistency params strategy
        eps delta gamma zeta hgood family hcons hd_zero
  have haxis_le_one : strategy.axisParallelFailureProbability ≤ 1 := by
    simpa [SymStrat.axisParallelFailureProbability] using
      bipartiteConsError_uniform_le_one strategy.state strategy.isNormalized
        (axisParallelPointAnswerFamily strategy)
        (axisParallelLineAnswerFamily strategy)
  have hself_le_one : strategy.selfConsistencyFailureProbability ≤ 1 := by
    simpa [SymStrat.selfConsistencyFailureProbability] using
      bipartiteSSCError_uniform_le_one strategy.state strategy.isNormalized
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
  have hgood_small : strategy.IsGood eps' delta' gamma := by
    refine ⟨?_, ?_, hgood.diagonalLineTest⟩
    · exact le_min hgood.axisParallelTest haxis_le_one
    · exact le_min hgood.selfConsistencyTest hself_le_one
  have hpoint_sdd :
      SDDRel strategy.state (uniformDistribution (Point params.next))
        (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas lineMeas))
        (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas pointMeas))
        (8 * (params.m : Error) * eps' + 4 * delta') := by
    have hpublic :=
      pointVerticalLineSdd_liftedVerticalLine_of_axis_self params strategy
        eps' delta' hgood_small.axisParallelTest hgood_small.selfConsistencyTest
    have hline_eq :
        IdxMeas.toIdxSubMeas lineMeas =
          liftedVerticalLineAnswerFamily params strategy := by
      funext u
      rfl
    have hpoint_eq :
        IdxMeas.toIdxSubMeas pointMeas =
          IdxProjMeas.toIdxSubMeas strategy.pointMeasurement := by
      funext u
      rfl
    rw [hline_eq, hpoint_eq]
    exact Preliminaries.sddRel_symm strategy.state
      (uniformDistribution (Point params.next)) _ _ _ hpublic
  have htri :
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (polynomialEvaluationFamily params.next
          (averagedSliceAppendedSubMeas params family))
        (IdxMeas.toIdxSubMeas pointMeas)
        ((min zeta 1 + Real.sqrt (8 * (params.m : Error) * eps' + 4 * delta')) +
          Real.sqrt (8 * (params.m : Error) * eps' + 4 * delta')) := by
    exact Preliminaries.triangleSub_right strategy.state
      (uniformDistribution (Point params.next))
      strategy.isNormalized
      (by simpa using uniformDistribution_weight_sum_le_one (Point params.next))
      (polynomialEvaluationFamily params.next
        (averagedSliceAppendedSubMeas params family))
      lineMeas pointMeas
      (min zeta 1 + Real.sqrt (8 * (params.m : Error) * eps' + 4 * delta'))
      (8 * (params.m : Error) * eps' + 4 * delta')
      hline hpoint_sdd
  have hswap :
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next
          (averagedSliceAppendedSubMeas params family))
        ((min zeta 1 + Real.sqrt (8 * (params.m : Error) * eps' + 4 * delta')) +
          Real.sqrt (8 * (params.m : Error) * eps' + 4 * delta')) := by
    exact consRel_symm_of_density_fixed strategy.state strategy.densityFixed
      (uniformDistribution (Point params.next))
      (polynomialEvaluationFamily params.next
        (averagedSliceAppendedSubMeas params family))
      (IdxMeas.toIdxSubMeas pointMeas)
      ((min zeta 1 + Real.sqrt (8 * (params.m : Error) * eps' + 4 * delta')) +
        Real.sqrt (8 * (params.m : Error) * eps' + 4 * delta'))
      htri
  exact ConsRel.mono (by
    simp [eps', delta']
    ring_nf
    exact le_rfl) hswap









end MIPStarRE.LDT.Pasting

end

end LIDT

open LIDT
/-!
# Section 12 pasting: degree-zero branch

Auxiliary constructions for the `d = 0` complementary branch of
`thm:ld-pasting`.

## References

- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters)
    [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (strategy : _root_.LIDT.MIPStarRE.LDT.SymStrat params.next ι)
    (eps delta gamma kappa zeta : _root_.LIDT.MIPStarRE.LDT.Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hd_zero : params.d = 0)
    (k : ℕ) :
    ∃ H : _root_.LIDT.MIPStarRE.LDT.Measurement (_root_.LIDT.MIPStarRE.LDT.Polynomial params.next) ι,
      H =
          _root_.LIDT.MIPStarRE.LDT.Preliminaries.completeAtOutcome
            (_root_.LIDT.MIPStarRE.LDT.Pasting.averagedSliceAppendedSubMeas params family)
            (_root_.LIDT.MIPStarRE.LDT.Pasting.pastedFallbackOutcome params) ∧
        _root_.LIDT.MIPStarRE.LDT.ConsRel strategy.state (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
          (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          (_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params.next H.toSubMeas)
          (_root_.LIDT.MIPStarRE.LDT.MainInductionStep.ldPastingInInductionError params k
            eps delta gamma kappa zeta) := by
  let S : _root_.LIDT.MIPStarRE.LDT.SubMeas (_root_.LIDT.MIPStarRE.LDT.Polynomial params.next) ι := _root_.LIDT.MIPStarRE.LDT.Pasting.averagedSliceAppendedSubMeas params family
  let H : _root_.LIDT.MIPStarRE.LDT.Measurement (_root_.LIDT.MIPStarRE.LDT.Polynomial params.next) ι :=
    _root_.LIDT.MIPStarRE.LDT.Preliminaries.completeAtOutcome S (_root_.LIDT.MIPStarRE.LDT.Pasting.pastedFallbackOutcome params)
  refine ⟨H, rfl, ?_⟩
  by_cases hk_pos : 1 ≤ k
  · let η : _root_.LIDT.MIPStarRE.LDT.Error := min zeta 1 +
      2 * Real.sqrt (8 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * min eps 1 + 4 * min delta 1)
    let ν : _root_.LIDT.MIPStarRE.LDT.Error := _root_.LIDT.MIPStarRE.LDT.MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta
    have hsubmeas :
        _root_.LIDT.MIPStarRE.LDT.ConsRel strategy.state (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
          (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          (_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params.next S) η := by
      simpa [S, η] using
        degreeZero_averagedSlice_pointConsistency params strategy eps delta gamma zeta
          hgood family hcons hd_zero
    let completedEval : _root_.LIDT.MIPStarRE.LDT.IdxSubMeas (_root_.LIDT.MIPStarRE.LDT.Point params.next) (_root_.LIDT.MIPStarRE.LDT.Fq params.next) ι :=
      fun u => (_root_.LIDT.MIPStarRE.LDT.Preliminaries.completeAtOutcome (_root_.LIDT.MIPStarRE.LDT.evaluateAt params.next u S)
        ((_root_.LIDT.MIPStarRE.LDT.Pasting.pastedFallbackOutcome params) u)).toSubMeas
    have hcompletedEval :
        completedEval = _root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params.next H.toSubMeas := by
      funext u
      simpa [completedEval, H, S, _root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily] using
        (_root_.LIDT.MIPStarRE.LDT.Preliminaries.evaluateAt_completeAtOutcome params.next S
          (_root_.LIDT.MIPStarRE.LDT.Pasting.pastedFallbackOutcome params) u).symm
    have hresidualMass :
        _root_.LIDT.MIPStarRE.LDT.ev strategy.state (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (1 - S.total)) ≤ kappa := by
      have hmass : _root_.LIDT.MIPStarRE.LDT.ev strategy.state (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) S.total) ≥ 1 - kappa := by
        simpa [S, _root_.LIDT.MIPStarRE.LDT.Pasting.averagedSliceAppendedSubMeas, _root_.LIDT.MIPStarRE.LDT.subMeasMass, _root_.LIDT.MIPStarRE.LDT.SubMeas.liftLeft,
          _root_.LIDT.MIPStarRE.LDT.postprocess_total] using hcomplete.averageCompleteness.lowerBound
      calc
        _root_.LIDT.MIPStarRE.LDT.ev strategy.state (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (1 - S.total))
          = _root_.LIDT.MIPStarRE.LDT.ev strategy.state (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (1 - S.total)) := by
              simpa using (strategy.permInvState.swap_ev (1 - S.total)).symm
        _ = 1 - _root_.LIDT.MIPStarRE.LDT.ev strategy.state (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) S.total) := by
              have hleftSub :
                  _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (1 - S.total) =
                    1 - _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) S.total := by
                ext i j
                rcases i with ⟨i₁, i₂⟩
                rcases j with ⟨j₁, j₂⟩
                by_cases h₁ : i₁ = j₁ <;> by_cases h₂ : i₂ = j₂ <;>
                  simp [_root_.LIDT.MIPStarRE.LDT.leftTensor, h₁, h₂, sub_eq_add_neg]
              rw [hleftSub, _root_.LIDT.MIPStarRE.LDT.ev_sub]
              simp [_root_.LIDT.MIPStarRE.LDT.ev_one_of_isNormalized strategy.state strategy.isNormalized]
        _ ≤ kappa := by linarith
    have hcompleted :
        _root_.LIDT.MIPStarRE.LDT.ConsRel strategy.state (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
          (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          completedEval (η + kappa) := by
      constructor
      calc
        _root_.LIDT.MIPStarRE.LDT.bipartiteConsError strategy.state (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
            (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
            completedEval
          ≤ _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next)) (fun u =>
              _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect strategy.state
                ((strategy.pointMeasurement u).toSubMeas)
                (_root_.LIDT.MIPStarRE.LDT.evaluateAt params.next u S) +
              _root_.LIDT.MIPStarRE.LDT.ev strategy.state (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (1 - S.total))) := by
                unfold _root_.LIDT.MIPStarRE.LDT.bipartiteConsError completedEval
                apply _root_.LIDT.MIPStarRE.LDT.avgOver_mono
                intro u
                simpa [S, _root_.LIDT.MIPStarRE.LDT.evaluateAt, _root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas, _root_.LIDT.MIPStarRE.LDT.postprocess_total] using
                  _root_.LIDT.MIPStarRE.LDT.Preliminaries.qBipartiteConsDefect_completeAtOutcome_right_le
                    strategy.state (strategy.pointMeasurement u).toMeasurement
                    (_root_.LIDT.MIPStarRE.LDT.evaluateAt params.next u S)
                    ((_root_.LIDT.MIPStarRE.LDT.Pasting.pastedFallbackOutcome params) u)
        _ = _root_.LIDT.MIPStarRE.LDT.bipartiteConsError strategy.state (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
              (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
              (_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params.next S) +
            _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
              (fun _ => _root_.LIDT.MIPStarRE.LDT.ev strategy.state (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (1 - S.total))) := by
                unfold _root_.LIDT.MIPStarRE.LDT.bipartiteConsError
                rw [_root_.LIDT.MIPStarRE.LDT.avgOver_add]
                simp [_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas, _root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily]
        _ ≤ η + _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
              (fun _ => _root_.LIDT.MIPStarRE.LDT.ev strategy.state (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (1 - S.total))) := by
                exact add_le_add hsubmeas.offDiagonalBound le_rfl
        _ = η + _root_.LIDT.MIPStarRE.LDT.ev strategy.state (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (1 - S.total)) := by
              simpa using _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_const (α := _root_.LIDT.MIPStarRE.LDT.Point params.next)
                (_root_.LIDT.MIPStarRE.LDT.ev strategy.state (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (1 - S.total)))
        _ ≤ η + kappa := by linarith
    have heps_nonneg : 0 ≤ eps := _root_.LIDT.MIPStarRE.LDT.eps_nonneg_of_isGood params.next strategy hgood
    have hdelta_nonneg : 0 ≤ delta := _root_.LIDT.MIPStarRE.LDT.delta_nonneg_of_isGood params.next strategy hgood
    have hgamma_nonneg : 0 ≤ gamma := _root_.LIDT.MIPStarRE.LDT.gamma_nonneg_of_isGood params.next strategy hgood
    have hzeta_nonneg : 0 ≤ zeta :=
      _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily.zeta_nonneg_of_consistentWithPoints strategy family hcons
    have hkappa_nonneg : 0 ≤ kappa :=
      _root_.LIDT.MIPStarRE.LDT.Pasting.kappa_nonneg_of_complete params strategy family hcomplete
    have heta_le : η ≤ 2 * ν := by
      simpa [η, ν] using
        degreeZero_submeas_error_le_two_nu params eps delta gamma zeta k hk_pos
          heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg
    have hkappa_le :
        kappa ≤ kappa * (1 + 1 / (100 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error))) := by
      have hcoef : (1 : _root_.LIDT.MIPStarRE.LDT.Error) ≤ 1 + 1 / (100 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error)) := by
        have hm_pos : (0 : _root_.LIDT.MIPStarRE.LDT.Error) < (params.m : _root_.LIDT.MIPStarRE.LDT.Error) := by exact_mod_cast params.hm
        have hden_pos : (0 : _root_.LIDT.MIPStarRE.LDT.Error) < 100 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) := by positivity
        have hfrac_nonneg : 0 ≤ (1 : _root_.LIDT.MIPStarRE.LDT.Error) / (100 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error)) :=
          div_nonneg zero_le_one hden_pos.le
        linarith
      simpa [one_mul] using mul_le_mul_of_nonneg_left hcoef hkappa_nonneg
    have herror_absorb :
        η + kappa ≤ _root_.LIDT.MIPStarRE.LDT.MainInductionStep.ldPastingInInductionError params k
          eps delta gamma kappa zeta := by
      have hexp_nonneg :
          0 ≤ Real.exp (-((k : _root_.LIDT.MIPStarRE.LDT.Error) / (80000 * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ))))) :=
        le_of_lt (Real.exp_pos _)
      change η + kappa ≤
        kappa * (1 + 1 / (100 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error))) + 2 * ν +
          Real.exp (-((k : _root_.LIDT.MIPStarRE.LDT.Error) / (80000 * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)))))
      nlinarith
    exact _root_.LIDT.MIPStarRE.LDT.ConsRel.mono herror_absorb (by simpa [hcompletedEval] using hcompleted)
  · have hk_zero : k = 0 := by omega
    exact _root_.LIDT.MIPStarRE.LDT.ConsRel.mono
      (_root_.LIDT.MIPStarRE.LDT.Pasting.one_le_ldPastingError_of_k_eq_zero params k eps delta gamma kappa zeta
        (_root_.LIDT.MIPStarRE.LDT.Pasting.kappa_nonneg_of_complete params strategy family hcomplete) hk_zero)
      ⟨_root_.LIDT.MIPStarRE.LDT.Pasting.bipartiteConsError_uniform_le_one strategy.state strategy.isNormalized
        (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params.next H.toSubMeas)⟩
