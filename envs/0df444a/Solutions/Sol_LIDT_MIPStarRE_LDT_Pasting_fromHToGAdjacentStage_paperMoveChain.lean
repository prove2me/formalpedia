-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.fromHToGAdjacentStage_paperMoveChain
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T16:24:54.950998+00:00
-- url     : https://prove2.me/submissions/b717af10-c623-4f93-b54b-ddaa91cf8735

-- Generated proof for MIPStarRE.LDT.Pasting.fromHToGAdjacentStage_paperMoveChain.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_Setup_Definitions
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
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.RingTheory.MvPolynomial.Basic
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_fromHToGAdjacentStageA0_eq_leftShape
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_fromHToGAdjacentStageM1_eq_halfSandwichLeftShape
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_fromHToGAdjacentStageM1_eq_rightShape
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_fromHToGAdjacentStageM2M3_paperMove
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_fromHToGAdjacentStageM2_eq_halfSandwichRightShape
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_fromHToGAdjacentStageM3E_paperMove
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_fromHToGStageMass_eq_adjacentStageA0
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_fromHToG_headTail_adjoint_qSDDCore_bound
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_fromHToG_selfConsistency_qSDDCore_bound
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_truncatedTypeSumRecurrence

open scoped _root_.Matrix

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

/- Source helpers from MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/Core/AveragesAndOps.lean. -/
/-!
# Section 12 pasting: operator averages and projective submeasurement lemmas

Averages over uniform distributions, tensor placement identities, and
projective submeasurement algebraic lemmas for the `fromHToG` reduction.
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]















/-- Conjugate transpose commutes with left tensor placement. -/
lemma fromHToG_leftTensor_conjTranspose (A : MIPStarRE.Quantum.Op ι) :
    (leftTensor (ι₂ := ι) A)ᴴ = leftTensor (ι₂ := ι) Aᴴ := by
  simp [leftTensor, Matrix.conjTranspose_kronecker]













end MIPStarRE.LDT.Pasting

end

/- Source helpers from MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/MoveLemmas/Basic.lean. -/
/-!
# Section 12 pasting: from-H-to-G move lemmas

Tensor, positivity, and Cauchy--Schwarz helper lemmas for the adjacent paper chain.
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma abs_sub_le_four (a b c d e : Error) :
    |a - e| ≤ |a - b| + |b - c| + |c - d| + |d - e| := by
  have h₁ : |a - e| ≤ |a - b| + |b - e| := abs_sub_le a b e
  have h₂ : |b - e| ≤ |b - c| + |c - e| := abs_sub_le b c e
  have h₃ : |c - e| ≤ |c - d| + |d - e| := abs_sub_le c d e
  linarith













/-- Completed `ĝ` measurement outcomes are Hermitian.  This records the
positivity-to-Hermitian conversion used when orienting the adjoint
half-sandwich commutator in the `M₂ → M₃` move. -/
lemma fromHToG_gHatIdxMeas_outcome_isHermitian
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x : Fq params) (g : GHatOutcome params) :
    ((gHatIdxMeas params family x).outcome g)ᴴ =
      (gHatIdxMeas params family x).outcome g := by
  exact (Matrix.nonneg_iff_posSemidef.mp
    ((gHatIdxMeas params family x).outcome_pos g)).isHermitian.eq















/-- Rewrite a nested finite sum as a sum over a product index. -/
lemma fromHToG_sum_product {α β : Type*} [Fintype α] [Fintype β]
    (F : α → β → Error) :
    (∑ a : α, ∑ b : β, F a b) = ∑ p : α × β, F p.1 p.2 := by
  rw [← Finset.univ_product_univ, Finset.sum_product]











end MIPStarRE.LDT.Pasting

end

/- Source helpers from MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/PaperBounds/SandwichContext.lean. -/
/-!
# Section 12 pasting: from-H-to-G S U S context-average bounds

Sandwich-sum identities and the `S U S` context-average bound used in the
second half-sandwich and final move-right Cauchy--Schwarz steps.
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The total mass of the tail sandwich family is the identity. -/
lemma fromHToG_gHatSandwichFamily_total_eq_one
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (n : ℕ) (xs : PointTuple params n) :
    (gHatSandwichFamily params family n xs).total = 1 := by
  simp [gHatSandwichFamily, gHatHalfProductTotalOperator_eq_one]

/-- The tail sandwich outcomes sum to the identity. -/
lemma fromHToG_gHatSandwichFamily_sum_eq_one
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (n : ℕ) (xs : PointTuple params n) :
    (∑ gs : GHatTupleOutcome params n,
      (gHatSandwichFamily params family n xs).outcome gs) = 1 := by
  rw [(gHatSandwichFamily params family n xs).sum_eq_total]
  exact fromHToG_gHatSandwichFamily_total_eq_one params family n xs











end MIPStarRE.LDT.Pasting

end

/- Source helpers from MIPStarRE/LDT/Pasting/Bernoulli/Weights.lean. -/
/-!
# Section 12 pasting: Bernoulli recurrence weights

Recurrence-weight identities for the `fromHToG` reduction.
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Bundle the four proved facts about the averaged total operator `G` used by
`fromHToGRecurrenceWeight` into a single `truncatedTypeSumRecurrence` call. -/
private lemma fromHToGRecurrenceWeight_recurrence
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (prefixLen : ℕ)
    {tailLen : ℕ} (τtail : GHatType tailLen) :
    (truncatedTypeSums family.averagedSubMeas.total params.d prefixLen τtail)ᴴ =
        truncatedTypeSums family.averagedSubMeas.total params.d prefixLen τtail ∧
      0 ≤ truncatedTypeSums family.averagedSubMeas.total params.d prefixLen τtail ∧
      truncatedTypeSums family.averagedSubMeas.total params.d prefixLen τtail ≤ 1 ∧
      truncatedTypeSums family.averagedSubMeas.total params.d (prefixLen + 1) τtail =
        truncatedTypeSums family.averagedSubMeas.total params.d prefixLen
            (prependTypeBit true τtail) * family.averagedSubMeas.total +
          truncatedTypeSums family.averagedSubMeas.total params.d prefixLen
            (prependTypeBit false τtail) * (1 - family.averagedSubMeas.total) :=
  truncatedTypeSumRecurrence family.averagedSubMeas.total
    family.averagedSubMeas.total_nonneg family.averagedSubMeas.total_le_one
    params.d prefixLen τtail

/-- `fromHToGRecurrenceWeight` is Hermitian (source-style API). -/
theorem fromHToGRecurrenceWeight_isHermitian
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (prefixLen : ℕ)
    {tailLen : ℕ} (τtail : GHatType tailLen) :
    (fromHToGRecurrenceWeight params family prefixLen τtail)ᴴ =
      fromHToGRecurrenceWeight params family prefixLen τtail :=
  (fromHToGRecurrenceWeight_recurrence params family prefixLen τtail).1

/-- `fromHToGRecurrenceWeight` is positive semidefinite (source-style API). -/
theorem fromHToGRecurrenceWeight_nonneg
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (prefixLen : ℕ)
    {tailLen : ℕ} (τtail : GHatType tailLen) :
    0 ≤ fromHToGRecurrenceWeight params family prefixLen τtail :=
  (fromHToGRecurrenceWeight_recurrence params family prefixLen τtail).2.1

/-- `fromHToGRecurrenceWeight` is bounded above by the identity. -/
theorem fromHToGRecurrenceWeight_le_one
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (prefixLen : ℕ)
    {tailLen : ℕ} (τtail : GHatType tailLen) :
    fromHToGRecurrenceWeight params family prefixLen τtail ≤ 1 :=
  (fromHToGRecurrenceWeight_recurrence params family prefixLen τtail).2.2.1







end MIPStarRE.LDT.Pasting

end

/- Source helpers from MIPStarRE/LDT/Preliminaries/CauchySchwarz.lean. -/
/-!
# Cauchy–Schwarz Inequalities for Approximate Measurements

Formalizes Cauchy–Schwarz-style propositions from Section 3
(Preliminaries) of the LDT paper:
- `easyApproxFromApproxDelta` — Proposition `prop:easy-approx-from-approx-delta`
- `closenessOfIP` / `closenessOfIPAdjoint` — Proposition `prop:closeness-of-ip`
  (`eq:closeness3` / `eq:closeness4`)
- `cabApproxDelta` — Proposition `prop:cab-approx-delta`

## References

- `references/ldt-paper/preliminaries.tex`
- `blueprint/src/chapter/ch03_preliminaries.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT







/-- `prop:closeness-of-ip` (`eq:closeness3`).

If `A ≈_γ B` (raw matrices) and `Σ_a (Σ_b C_{a,b})(Σ_b C_{a,b})† ≤ I`,
then
`|𝔼_x Σ_{a,b} ⟨ψ| C_{a,b} A_a |ψ⟩ -
  𝔼_x Σ_{a,b} ⟨ψ| C_{a,b} B_a |ψ⟩| ≤ √γ`. -/
theorem closenessOfIP
    {Question OutcomeA OutcomeB : Type*} {ι : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized)
    (𝒟 : Distribution Question)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A B : Question → OutcomeA → MIPStarRE.Quantum.Op ι)
    (C : Question → OutcomeA → OutcomeB → MIPStarRE.Quantum.Op ι)
    (γ : Error)
    (hAB : avgOver 𝒟 (fun q => qSDDCore ψ (A q) (B q)) ≤ γ)
    (hC :
      ∀ q,
        ∑ a : OutcomeA,
          (∑ b : OutcomeB, C q a b) * (∑ b : OutcomeB, C q a b)ᴴ ≤ 1) :
    |avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * A q a)) -
        avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * B q a))| ≤
      Real.sqrt γ := by
  simpa using closenessOfInnerProduct_left ψ hψ 𝒟 h𝒟 A B C γ hAB hC

/-- `prop:closeness-of-ip` (`eq:closeness4`, adjoint version).

If `A† ≈_γ B†` and `Σ_a (Σ_b C_{a,b})†(Σ_b C_{a,b}) ≤ I`, then
`|𝔼_x Σ_{a,b} ⟨ψ| A_a C_{a,b} |ψ⟩ -
  𝔼_x Σ_{a,b} ⟨ψ| B_a C_{a,b} |ψ⟩| ≤ √γ`. -/
theorem closenessOfIPAdjoint
    {Question OutcomeA OutcomeB : Type*} {ι : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized)
    (𝒟 : Distribution Question)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A B : Question → OutcomeA → MIPStarRE.Quantum.Op ι)
    (C : Question → OutcomeA → OutcomeB → MIPStarRE.Quantum.Op ι)
    (γ : Error)
    (hAB :
      avgOver 𝒟
        (fun q => qSDDCore ψ (fun a => (A q a)ᴴ) (fun a => (B q a)ᴴ)) ≤ γ)
    (hC :
      ∀ q,
        ∑ a : OutcomeA,
          (∑ b : OutcomeB, C q a b)ᴴ * (∑ b : OutcomeB, C q a b) ≤ 1) :
    |avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (A q a * C q a b)) -
        avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (B q a * C q a b))| ≤
      Real.sqrt γ := by
  simpa using closenessOfInnerProduct_right ψ hψ 𝒟 h𝒟 A B C γ hAB hC



end MIPStarRE.LDT.Preliminaries

end

end LIDT

open LIDT
/-!
# Section 12 pasting: from-H-to-G paper telescope

This file assembles the adjacent-stage paper move chain and records the final
stage-mass telescope for the `fromHToG` reduction.
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters)
    [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (ψbi : _root_.LIDT.MIPStarRE.LDT.QuantumState (ι × ι))
    (hnorm : ψbi.IsNormalized)
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    (gamma zeta : _root_.LIDT.MIPStarRE.LDT.Error)
    (hgamma_nonneg : 0 ≤ gamma) (hzeta_nonneg : 0 ≤ zeta)
    (hfacts : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatFactsStatement params ψbi family gamma zeta)
    (hhalf : ∀ j : ℕ, 2 ≤ j →
      _root_.LIDT.MIPStarRE.LDT.Pasting.CommuteGHalfSandwichStatement params ψbi family gamma zeta j)
    (hstageExact : _root_.LIDT.MIPStarRE.LDT.Pasting.FromHToGAdjacentStageExactFacts params ψbi family)
    (k ℓ : ℕ) (hℓ : ℓ < k) :
    |_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGStageMass params ψbi family k ℓ -
        _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGStageMass params ψbi family k (ℓ + 1)| ≤
      _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceError params gamma zeta k := by
  let A : _root_.LIDT.MIPStarRE.LDT.Error := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGStageMass params ψbi family k ℓ
  let E : _root_.LIDT.MIPStarRE.LDT.Error := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGStageMass params ψbi family k (ℓ + 1)
  let M₁ : _root_.LIDT.MIPStarRE.LDT.Error := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGAdjacentStageM1 params ψbi family k ℓ
  let M₂ : _root_.LIDT.MIPStarRE.LDT.Error := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGAdjacentStageM2 params ψbi family k ℓ
  let M₃ : _root_.LIDT.MIPStarRE.LDT.Error := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGAdjacentStageM3 params ψbi family k ℓ
  let M₄ : _root_.LIDT.MIPStarRE.LDT.Error := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGAdjacentStageM4 params ψbi family k ℓ
  let Collapsed : _root_.LIDT.MIPStarRE.LDT.Error := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGAdjacentStageCollapsed params ψbi family k ℓ
  have hA₁ : |A - M₁| ≤ Real.sqrt (2 * zeta) := by
    have hA_eq_A0 : A = _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGAdjacentStageA0 params ψbi family k ℓ := by
      simpa [A] using _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGStageMass_eq_adjacentStageA0 params ψbi family hℓ
    let n := k - (ℓ + 1)
    have hA0M1_secondRoot_le :
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n)) (fun q =>
          _root_.LIDT.MIPStarRE.LDT.qSDDCore ψbi
            (fun g : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params =>
              _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome g))
            (fun g : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params =>
              _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome g))) ≤
          2 * zeta := by
      simpa [n] using
        _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_selfConsistency_qSDDCore_bound params ψbi family zeta
          hfacts.completedSelfConsistency (n := n)
    have hA0M1_moveRight :
        |_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGAdjacentStageA0 params ψbi family k ℓ -
            _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGAdjacentStageM1 params ψbi family k ℓ| ≤ Real.sqrt (2 * zeta) := by
      let Aop : _root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n → _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params →
          _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) := fun q g =>
        _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome g)
      let Bop : _root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n → _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params →
          _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) := fun q g =>
        _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome g)
      let C : _root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n → _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params →
          _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n → _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) := fun q g gs =>
        let S := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight params family ℓ
          (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit g.isSome (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType gs))
        let U := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome g
        let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 gs
        _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (U * T * Tᴴ) * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) S
      have hA0M1_firstRoot_le_one : ∀ q : _root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n,
          ∑ g : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params,
            (∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n, C q g gs) *
              (∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n, C q g gs)ᴴ ≤ 1 := by
        /- Paper lines 1472--1478: the first square root in
        `eq:call-again-later-part-tres` is exactly the `Ĥ ⊗ S²` term, so this
        should be discharged by rewriting `A0` as a suffix `Ĥ`, using
        `eq:S-bound`, and then applying submeasurement boundedness. -/
        intro q
        let tailBlock : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params → _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) := fun g =>
          ∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n,
            let S := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight params family ℓ
              (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit g.isSome (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType gs))
            let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 gs
            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (T * Tᴴ) * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) S
        have htail_expand : ∀ g : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params,
            ∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n, C q g gs =
              _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome g) *
                tailBlock g := by
          intro g
          dsimp [tailBlock, C]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro gs _hgs
          calc
            _root_.LIDT.MIPStarRE.LDT.leftTensor
                ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome g *
                  _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 gs *
                    (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 gs)ᴴ) *
                _root_.LIDT.MIPStarRE.LDT.rightTensor
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight params family ℓ
                    (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit g.isSome (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType gs)))
              = _root_.LIDT.MIPStarRE.LDT.leftTensor
                  ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome g *
                    (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 gs *
                      (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 gs)ᴴ)) *
                _root_.LIDT.MIPStarRE.LDT.rightTensor
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight params family ℓ
                    (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit g.isSome (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType gs))) := by
                        simp [mul_assoc]
            _ = (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome g) *
                  _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                    (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 gs *
                      (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 gs)ᴴ)) *
                  _root_.LIDT.MIPStarRE.LDT.rightTensor
                    (_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight params family ℓ
                      (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit g.isSome (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType gs))) := by
                        rw [← _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_leftTensor]
            _ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome g) *
                  (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                      (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 gs *
                        (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 gs)ᴴ) *
                    _root_.LIDT.MIPStarRE.LDT.rightTensor
                      (_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight params family ℓ
                        (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit g.isSome (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType gs)))) := by
                          simp [mul_assoc]
        have htail_pos : ∀ g : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params, 0 ≤ tailBlock g := by
          intro g
          dsimp [tailBlock]
          refine Finset.sum_nonneg ?_
          intro gs _hgs
          let S := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight params family ℓ
            (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit g.isSome (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType gs))
          let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 gs
          have hTT_pos : 0 ≤ T * Tᴴ := by
            have hpos : 0 ≤ (Tᴴ)ᴴ * Tᴴ :=
              (CStarAlgebra.nonneg_iff_eq_star_mul_self).2 ⟨Tᴴ, rfl⟩
            simpa using hpos
          have hS_pos : 0 ≤ S :=
            _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight_nonneg params family ℓ
              (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit g.isSome (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType gs))
          rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor]
          exact _root_.LIDT.MIPStarRE.Quantum.kronecker_nonneg hTT_pos hS_pos
        have htail_le_one : ∀ g : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params, tailBlock g ≤ 1 := by
          intro g
          let sandTerm : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n → _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) := fun gs =>
            let S := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight params family ℓ
              (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit g.isSome (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType gs))
            let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 gs
            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (T * Tᴴ) * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) S
          let sandLeft : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n → _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) := fun gs =>
            let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 gs
            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (T * Tᴴ)
          calc
            tailBlock g = ∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n, sandTerm gs := by
              simp [tailBlock, sandTerm]
            _ ≤ ∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n, sandLeft gs := by
                    refine Finset.sum_le_sum ?_
                    intro gs _hgs
                    let S := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight params family ℓ
                      (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit g.isSome (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType gs))
                    let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 gs
                    have hTT_pos : 0 ≤ T * Tᴴ := by
                      have hpos : 0 ≤ (Tᴴ)ᴴ * Tᴴ :=
                        (CStarAlgebra.nonneg_iff_eq_star_mul_self).2 ⟨Tᴴ, rfl⟩
                      simpa using hpos
                    have hS_le : S ≤ 1 :=
                      _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight_le_one params family ℓ
                        (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit g.isSome (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType gs))
                    dsimp [sandTerm, sandLeft]
                    rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor]
                    simpa [sandTerm, sandLeft, T, _root_.LIDT.MIPStarRE.LDT.leftTensor, _root_.LIDT.MIPStarRE.LDT.opTensor] using
                      _root_.LIDT.MIPStarRE.LDT.opTensor_mono_right (A := T * Tᴴ) hTT_pos hS_le
            _ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                  (∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n,
                    let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 gs
                    T * Tᴴ) := by
                      simp [sandLeft, _root_.LIDT.MIPStarRE.LDT.leftTensor_finset_sum]
            _ = 1 := by
                  have hsum :
                      (∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n,
                        let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 gs
                        T * Tᴴ) = 1 := by
                    simpa [_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSandwichFamily] using
                      _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_gHatSandwichFamily_sum_eq_one params family n q.2
                  rw [hsum]
                  simp [_root_.LIDT.MIPStarRE.LDT.leftTensor]
        have htail_sq_le_self : ∀ g : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params,
            tailBlock g * tailBlock g ≤ tailBlock g := by
          intro g
          exact _root_.LIDT.MIPStarRE.Quantum.sq_le_self (htail_pos g) (htail_le_one g)
        have hterm_le : ∀ g : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params,
            (∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n, C q g gs) *
                (∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n, C q g gs)ᴴ ≤
              _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome g) := by
          intro g
          let U := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome g
          have hU_herm : (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) U)ᴴ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) U := by
            simpa [U, _root_.LIDT.MIPStarRE.LDT.leftTensor, _root_.LIDT.MIPStarRE.LDT.opTensor,
              _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_gHatIdxMeas_outcome_isHermitian params family q.1 g] using
              (_root_.LIDT.MIPStarRE.LDT.conjTranspose_opTensor U (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι))
          have hU_pos : 0 ≤ _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) U := by
            exact _root_.LIDT.MIPStarRE.LDT.leftTensor_nonneg (ι₂ := ι) ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome_pos g)
          have hU_le : _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) U ≤ 1 := by
            exact _root_.LIDT.MIPStarRE.LDT.leftTensor_le_one (ι₂ := ι) ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome_le_one g)
          calc
            (∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n, C q g gs) *
                (∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n, C q g gs)ᴴ
              = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) U * (tailBlock g * tailBlock g) *
                  _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) U := by
                  rw [htail_expand g, Matrix.conjTranspose_mul, hU_herm]
                  have htail_herm : (tailBlock g)ᴴ = tailBlock g := by
                    exact (Matrix.nonneg_iff_posSemidef.mp (htail_pos g)).isHermitian.eq
                  rw [htail_herm]
                  simp [mul_assoc, U]
            _ ≤ _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) U * tailBlock g * _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) U := by
                  exact IsSelfAdjoint.conjugate_le_conjugate (htail_sq_le_self g) hU_herm
            _ ≤ _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) U * 1 * _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) U := by
                  exact IsSelfAdjoint.conjugate_le_conjugate (htail_le_one g) hU_herm
            _ ≤ _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) U := by
                  calc
                    _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) U * 1 * _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) U
                      = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) U * _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) U := by simp
                    _ ≤ _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) U := by
                      simpa [_root_.LIDT.MIPStarRE.LDT.leftTensor_mul_leftTensor] using
                        _root_.LIDT.MIPStarRE.Quantum.sq_le_self hU_pos hU_le
        calc
          ∑ g : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params,
              (∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n, C q g gs) *
                (∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n, C q g gs)ᴴ
            ≤ ∑ g : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params,
                _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome g) := by
                  exact Finset.sum_le_sum (fun g _hg => hterm_le g)
          _ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                (∑ g : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params, (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome g) := by
                  rw [← _root_.LIDT.MIPStarRE.LDT.leftTensor_finset_sum (ι₂ := ι) Finset.univ
                    (fun g : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params => (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome g)]
          _ = 1 := by
                rw [(_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).sum_eq_total]
                rw [(_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).total_eq_one]
                simp [_root_.LIDT.MIPStarRE.LDT.leftTensor]
      have hA0M1_cauchySchwarz := _root_.LIDT.MIPStarRE.LDT.Preliminaries.closenessOfIP ψbi hnorm
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n))
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_weight_sum_le_one (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n))
        Aop Bop C (2 * zeta) (by simpa [Aop, Bop] using hA0M1_secondRoot_le)
        hA0M1_firstRoot_le_one
      simpa [Aop, Bop, C, _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGAdjacentStageA0_eq_leftShape,
        _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGAdjacentStageM1_eq_rightShape] using hA0M1_cauchySchwarz
    simpa [hA_eq_A0, M₁] using hA0M1_moveRight
  have h₁₂ : |M₁ - M₂| ≤ Real.sqrt (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwichError params gamma zeta k) := by
    /- Paper lines 1495--1550.  This is the first half-sandwich commutation:
    first rewrite `eq:move-g-over-there` into the source/target forms of
    `eq:commute-g-part-one`, then apply the Cauchy--Schwarz estimate
    `eq:call-this-later`, with the two square roots handled separately. -/
    let n := k - (ℓ + 1)
    by_cases hn0 : n = 0
    · have hM₁ : M₁ =
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n)) fun q =>
            ∑ g : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params, ∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n,
              let S := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight params family ℓ
                (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit g.isSome (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType gs))
              let U := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome g
              let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 gs
              _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (U * T) *
                (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) Tᴴ * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (S * U))) := by
        simpa [M₁, n] using
          _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGAdjacentStageM1_eq_halfSandwichLeftShape params ψbi family k ℓ
      have hM₂ : M₂ =
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n)) fun q =>
            ∑ g : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params, ∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n,
              let S := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight params family ℓ
                (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit g.isSome (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType gs))
              let U := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome g
              let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 gs
              _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (T * U) *
                (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) Tᴴ * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (S * U))) := by
        simpa only [M₂] using
          _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGAdjacentStageM2_eq_halfSandwichRightShape params ψbi family k ℓ
      have hM : M₁ = M₂ := by
        rw [hM₁, hM₂]
        rw [hn0]
        simp [_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator]
      rw [hM, sub_self, abs_zero]
      exact Real.sqrt_nonneg _
    · have hnpos : 1 ≤ n := Nat.pos_iff_ne_zero.mpr hn0
      have hn : 2 ≤ n + 1 := Nat.succ_le_succ hnpos
      have hnk : n + 1 ≤ k := by
        dsimp [n]
        omega
      have hM₁_source : M₁ =
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n)) fun q =>
            ∑ g : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params, ∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n,
              let S := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight params family ℓ
                (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit g.isSome (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType gs))
              let U := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome g
              let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 gs
              _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (U * T) *
                (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) Tᴴ * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (S * U))) := by
        simpa [M₁, n] using
          _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGAdjacentStageM1_eq_halfSandwichLeftShape params ψbi family k ℓ
      have hM₂_target : M₂ =
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n)) fun q =>
            ∑ g : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params, ∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n,
              let S := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight params family ℓ
                (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit g.isSome (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType gs))
              let U := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome g
              let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 gs
              _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (T * U) *
                (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) Tᴴ * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (S * U))) := by
        simpa [M₂, n] using
          _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGAdjacentStageM2_eq_halfSandwichRightShape params ψbi family k ℓ
      have h₁₂_secondRoot_le_nu4 :
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n)) (fun q =>
            _root_.LIDT.MIPStarRE.LDT.qSDDCore ψbi
              (fun ogs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n =>
                _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                  ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 ogs.2)ᴴ *
                    (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ogs.1))
              (fun ogs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n =>
                _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                  ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ogs.1 *
                    (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 ogs.2)ᴴ))) ≤
            _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwichError params gamma zeta k := by
        simpa [n] using
          _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_headTail_adjoint_qSDDCore_bound params ψbi family gamma zeta
            hgamma_nonneg hzeta_nonneg hhalf (n := n) (k := k) hn hnk
      have h₁₂_firstRoot_le_one :
          ∀ q : _root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n,
            ∑ ogs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n,
              (∑ _u : Unit,
                let S := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight params family ℓ
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit ogs.1.isSome (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType ogs.2))
                let U := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ogs.1
                let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 ogs.2
                _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) Tᴴ * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (S * U))ᴴ *
              (∑ _u : Unit,
                let S := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight params family ℓ
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit ogs.1.isSome (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType ogs.2))
                let U := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ogs.1
                let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 ogs.2
                _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) Tᴴ * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (S * U)) ≤ 1 := by
        /- Paper lines 1531--1550: the first square root in
        `eq:call-this-later` is rewritten to a suffix `Ĥ` term, bounded by
        `S ≤ I`, then by projectivity `U^2 = U`, and finally by the fact that
        both `ĝ` and `Ĥ` are submeasurements. -/
        intro q
        have hterm_le : ∀ ogs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n,
            (∑ _u : Unit,
              let S := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight params family ℓ
                (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit ogs.1.isSome (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType ogs.2))
              let U := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ogs.1
              let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 ogs.2
              _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) Tᴴ * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (S * U))ᴴ *
            (∑ _u : Unit,
              let S := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight params family ℓ
                (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit ogs.1.isSome (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType ogs.2))
              let U := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ogs.1
              let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 ogs.2
              _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) Tᴴ * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (S * U)) ≤
              _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 ogs.2 *
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 ogs.2)ᴴ) *
                _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ogs.1) := by
          intro ogs
          let S := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight params family ℓ
            (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit ogs.1.isSome (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType ogs.2))
          let U := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ogs.1
          let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 ogs.2
          have hTpos : 0 ≤ T * Tᴴ := by
            have hpos : 0 ≤ (Tᴴ)ᴴ * Tᴴ :=
              (CStarAlgebra.nonneg_iff_eq_star_mul_self).2 ⟨Tᴴ, rfl⟩
            simpa using hpos
          have hUherm : Uᴴ = U := by
            simpa [U] using _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_gHatIdxMeas_outcome_isHermitian params family q.1 ogs.1
          have hSU_le : (S * U)ᴴ * (S * U) ≤ U := by
            have hSsq : S * S ≤ 1 := by
              exact le_trans (_root_.LIDT.MIPStarRE.Quantum.sq_le_self
                (_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight_nonneg params family ℓ
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit ogs.1.isSome (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType ogs.2)))
                (_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight_le_one params family ℓ
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit ogs.1.isSome (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType ogs.2))))
                (_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight_le_one params family ℓ
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit ogs.1.isSome (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType ogs.2)))
            calc
              (S * U)ᴴ * (S * U) = U * (S * S) * U := by
                simp [Matrix.conjTranspose_mul, hUherm, S, U, mul_assoc,
                  _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight_isHermitian]
              _ ≤ U * 1 * U := IsSelfAdjoint.conjugate_le_conjugate hSsq hUherm
              _ ≤ U := by
                have hUpos : 0 ≤ U := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome_pos ogs.1
                have hUle : U ≤ 1 := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome_le_one ogs.1
                simpa using _root_.LIDT.MIPStarRE.Quantum.sq_le_self hUpos hUle
          calc
            (∑ _u : Unit, _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) Tᴴ * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (S * U))ᴴ *
                (∑ _u : Unit, _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) Tᴴ * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (S * U))
              = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (T * Tᴴ) *
                  _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((S * U)ᴴ * (S * U)) := by
                    rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor,
                      _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor]
                    simp [_root_.LIDT.MIPStarRE.LDT.conjTranspose_opTensor, _root_.LIDT.MIPStarRE.LDT.opTensor_mul, Matrix.conjTranspose_mul,
                      hUherm, _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight_isHermitian, S, U, mul_assoc]
            _ ≤ _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (T * Tᴴ) * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) U := by
                  rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor,
                    _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor]
                  exact _root_.LIDT.MIPStarRE.LDT.opTensor_mono_right hTpos hSU_le
        calc
          ∑ ogs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n,
              (∑ _u : Unit,
                let S := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight params family ℓ
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit ogs.1.isSome (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType ogs.2))
                let U := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ogs.1
                let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 ogs.2
                _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) Tᴴ * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (S * U))ᴴ *
              (∑ _u : Unit,
                let S := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight params family ℓ
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit ogs.1.isSome (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType ogs.2))
                let U := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ogs.1
                let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 ogs.2
                _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) Tᴴ * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (S * U))
            ≤ ∑ ogs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n,
                _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 ogs.2 *
                    (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 ogs.2)ᴴ) *
                  _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ogs.1) := by
                exact Finset.sum_le_sum (fun ogs _ => hterm_le ogs)
          _ = 1 := by
                calc
                  ∑ ogs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n,
                      _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                        (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 ogs.2 *
                          (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 ogs.2)ᴴ) *
                        _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ogs.1)
                    = ∑ g : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params, ∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n,
                        _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                          (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 gs *
                            (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 gs)ᴴ) *
                          _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
                            ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome g) := by
                        rw [← Finset.univ_product_univ, Finset.sum_product]
                  _ = ∑ g : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params,
                        _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome g) := by
                        refine Finset.sum_congr rfl ?_
                        intro g _hg
                        rw [← Finset.sum_mul]
                        rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_finset_sum]
                        have hsum :
                            (∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n,
                              let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 gs
                              T * Tᴴ) = 1 := by
                          simpa [_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSandwichFamily] using
                            _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_gHatSandwichFamily_sum_eq_one params family n q.2
                        rw [hsum]
                        simp [_root_.LIDT.MIPStarRE.LDT.leftTensor]
                  _ = 1 := by
                        rw [_root_.LIDT.MIPStarRE.LDT.rightTensor_finset_sum]
                        rw [(_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).sum_eq_total]
                        rw [(_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).total_eq_one]
                        simp [_root_.LIDT.MIPStarRE.LDT.rightTensor]
      have h₁₂_cauchySchwarz :
          |M₁ - M₂| ≤ Real.sqrt (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwichError params gamma zeta k) := by
        /- Paper lines 1506--1523.  Rewrite `hM₁_source` and `hM₂_target` as a
        product-index sum over `(g, gs)`, insert a dummy `Unit` outcome so that
        `closenessOfIPAdjoint` applies, use `h₁₂_secondRoot_le_nu4` for the
        commutator square, and discharge the context side condition using the
        bound sketched in `h₁₂_firstRoot_le_one`. -/
        let Aop : _root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n →
            _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n →
            _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) := fun q ogs =>
          let U := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ogs.1
          let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 ogs.2
          _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (U * T)
        let Bop : _root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n →
            _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n →
            _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) := fun q ogs =>
          let U := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ogs.1
          let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 ogs.2
          _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (T * U)
        let Cop : _root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n →
            _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n → Unit →
            _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) := fun q ogs _ =>
          let S := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight params family ℓ
            (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit ogs.1.isSome (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType ogs.2))
          let U := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ogs.1
          let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 ogs.2
          _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) Tᴴ * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (S * U)
        have hAB_adj :
            _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n)) (fun q =>
              _root_.LIDT.MIPStarRE.LDT.qSDDCore ψbi (fun ogs => (Aop q ogs)ᴴ) (fun ogs => (Bop q ogs)ᴴ)) ≤
              _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwichError params gamma zeta k := by
          simpa [Aop, Bop, _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_leftTensor_conjTranspose, Matrix.conjTranspose_mul,
              _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_gHatIdxMeas_outcome_isHermitian] using h₁₂_secondRoot_le_nu4
        have hC_adj : ∀ q : _root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n,
            ∑ ogs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n,
              (∑ u : Unit, Cop q ogs u)ᴴ * (∑ u : Unit, Cop q ogs u) ≤ 1 := by
          intro q
          simpa only [Cop] using h₁₂_firstRoot_le_one q
        have hcs := _root_.LIDT.MIPStarRE.LDT.Preliminaries.closenessOfIPAdjoint ψbi hnorm
          (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n))
          (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_weight_sum_le_one (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n))
          Aop Bop Cop (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwichError params gamma zeta k)
          hAB_adj hC_adj
        have hM₁_prod : M₁ =
            _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n)) fun q =>
              ∑ ogs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n,
                let S := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight params family ℓ
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit ogs.1.isSome (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType ogs.2))
                let U := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ogs.1
                let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 ogs.2
                _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (U * T) *
                  (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) Tᴴ * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (S * U))) := by
          rw [hM₁_source]
          refine _root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ ?_
          intro q
          exact _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_sum_product (fun g gs =>
            let S := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight params family ℓ
              (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit g.isSome (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType gs))
            let U := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome g
            let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 gs
            _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (U * T) *
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) Tᴴ * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (S * U))))
        have hM₂_prod : M₂ =
            _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n)) fun q =>
              ∑ ogs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n,
                let S := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight params family ℓ
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit ogs.1.isSome (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType ogs.2))
                let U := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ogs.1
                let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 ogs.2
                _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (T * U) *
                  (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) Tᴴ * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (S * U))) := by
          rw [hM₂_target]
          refine _root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ ?_
          intro q
          exact _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_sum_product (fun g gs =>
            let S := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight params family ℓ
              (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit g.isSome (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType gs))
            let U := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome g
            let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 gs
            _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (T * U) *
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) Tᴴ * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (S * U))))
        simpa [Aop, Bop, Cop, hM₁_prod, hM₂_prod] using hcs
      exact h₁₂_cauchySchwarz
  have h₂₃ : |M₂ - M₃| ≤ Real.sqrt (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwichError params gamma zeta k) := by
    simpa [M₂, M₃] using
      _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGAdjacentStageM2M3_paperMove params ψbi hnorm family gamma zeta
        hgamma_nonneg hzeta_nonneg hhalf hstageExact k ℓ
  have hmove₂ : |M₃ - E| ≤ Real.sqrt (2 * zeta) := by
    simpa [M₃, E] using
      _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGAdjacentStageM3E_paperMove params ψbi hnorm family gamma zeta
        hfacts hstageExact k ℓ
  have hchain :
      |A - E| ≤ Real.sqrt (2 * zeta) +
          Real.sqrt (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwichError params gamma zeta k) +
          Real.sqrt (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwichError params gamma zeta k) +
          Real.sqrt (2 * zeta) := by
    have htel := _root_.LIDT.MIPStarRE.LDT.Pasting.abs_sub_le_four A M₁ M₂ M₃ E
    linarith
  calc
    |_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGStageMass params ψbi family k ℓ -
        _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGStageMass params ψbi family k (ℓ + 1)| = |A - E| := rfl
    _ ≤ Real.sqrt (2 * zeta) +
          Real.sqrt (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwichError params gamma zeta k) +
          Real.sqrt (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwichError params gamma zeta k) +
          Real.sqrt (2 * zeta) := hchain
    _ = _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceError params gamma zeta k := by
          simp [_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceError, Real.sqrt_eq_rpow]
          ring
