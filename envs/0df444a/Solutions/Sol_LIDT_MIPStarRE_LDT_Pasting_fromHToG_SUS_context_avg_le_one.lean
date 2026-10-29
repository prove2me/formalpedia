-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.fromHToG_SUS_context_avg_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T16:05:43.370021+00:00
-- url     : https://prove2.me/submissions/53e9cc5d-f3ab-46ee-8eba-64a4dd7f1397

-- Generated proof for MIPStarRE.LDT.Pasting.fromHToG_SUS_context_avg_le_one.
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_fromHToG_avgOver_head_ev_sandwich
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_fromHToG_avgOver_tail_type_ev
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_fromHToG_bool_type_filtered_outcome_sum
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_fromHToG_ev_sum_isSome_sandwich_weight
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_fromHToG_sum_2_avgOver_2
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_fromHToG_sum_averagedSandwichByType_total_eq_one
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_psd_contraction_comm_sandwich_le
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













/-- Right tensor placement distributes over addition. -/
lemma fromHToG_rightTensor_add (A B : MIPStarRE.Quantum.Op ι) :
    rightTensor (ι₁ := ι) (A + B) =
      rightTensor (ι₁ := ι) A + rightTensor (ι₁ := ι) B := by
  simpa [Fintype.sum_bool] using
    (rightTensor_finset_sum (ι₁ := ι) (Finset.univ : Finset Bool)
      (fun b : Bool => if b then A else B)).symm















end MIPStarRE.LDT.Pasting

end

/- Source helpers from MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/MoveLemmas/TailStage.lean. -/
/-!
# Section 12 pasting: from-H-to-G head-tail stage reindexing

The head-tail reindexing lemmas for the adjacent-stage source expression in the
paper's `from H to G` chain.
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]







/-- Fold a tail point/outcome average written directly with the sandwich-family
outcomes into `averagedSandwichByTypeSubMeas`. -/
lemma fromHToG_avgOver_tail_type_ev_sandwich
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (n : ℕ) (τ : GHatType n)
    (B : MIPStarRE.Quantum.Op ι) :
    avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
      ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
          gHatTupleType gs = τ,
        ev ψbi (leftTensor (ι₂ := ι)
          ((gHatSandwichFamily params family n xs).outcome gs) *
            rightTensor (ι₁ := ι) B)) =
      ev ψbi (leftTensor (ι₂ := ι)
        (averagedSandwichByTypeSubMeas params family n τ).total *
          rightTensor (ι₁ := ι) B) := by
  simpa [gHatSandwichFamily] using
    (fromHToG_avgOver_tail_type_ev params ψbi family n τ B)



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









/-- Fold the complete/incomplete head branch average with an `S · B · S`
sandwich into the stored exact branch averages. -/
lemma fromHToG_avgOver_head_branch_ev_sandwich
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (hcomplete : averageOperatorOverDistribution (uniformDistribution (Fq params))
      (fun x => (completePartSubMeas params family x).total) =
        family.averagedSubMeas.total)
    (hincomplete : averageOperatorOverDistribution (uniformDistribution (Fq params))
      (fun x => (incompletePartSubMeas params family x).total) =
        1 - family.averagedSubMeas.total)
    (b : Bool) (A S : MIPStarRE.Quantum.Op ι) :
    avgOver (uniformDistribution (Fq params)) (fun x =>
      let B := if b then (completePartSubMeas params family x).total
        else (incompletePartSubMeas params family x).total
      ev ψbi (leftTensor (ι₂ := ι) A * rightTensor (ι₁ := ι) (S * B * S))) =
      ev ψbi (leftTensor (ι₂ := ι) A *
        rightTensor (ι₁ := ι)
          (S * (if b then family.averagedSubMeas.total
            else 1 - family.averagedSubMeas.total) * S)) := by
  cases b
  · rw [fromHToG_avgOver_head_ev_sandwich]
    simp only [Bool.false_eq_true, ite_false]
    rw [hincomplete]
  · rw [fromHToG_avgOver_head_ev_sandwich]
    simp only [ite_true]
    rw [hcomplete]





end MIPStarRE.LDT.Pasting

end

/- Source helpers from MIPStarRE/LDT/Pasting/Bernoulli/TruncatedSums.lean. -/
/-!
# Section 12 pasting: Bernoulli truncated sums

Truncated type sums and their one-step recurrence.
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Bernoulli recurrence weights -/













/-- Each Boolean-type monomial commutes with the base operator `G`. -/
lemma gHatTypeOperator_commute_base
    (G : MIPStarRE.Quantum.Op ι) {k : ℕ} (τ : GHatType k) :
    Commute (gHatTypeOperator G τ) G := by
  have hcomm : Commute G (1 - G) := (Commute.one_right G).sub_right (Commute.refl G)
  have hleft : Commute (G ^ gHatTypeWeight τ) G := (Commute.refl G).pow_left _
  have hright : Commute ((1 - G) ^ (k - gHatTypeWeight τ)) G := hcomm.symm.pow_left _
  unfold gHatTypeOperator
  exact hleft.mul_left hright

/-- Each Boolean-type monomial commutes with the complementary base operator `1 - G`. -/
lemma gHatTypeOperator_commute_one_sub_base
    (G : MIPStarRE.Quantum.Op ι) {k : ℕ} (τ : GHatType k) :
    Commute (gHatTypeOperator G τ) (1 - G) := by
  have hcomm : Commute G (1 - G) := (Commute.one_right G).sub_right (Commute.refl G)
  have hleft : Commute (G ^ gHatTypeWeight τ) (1 - G) := hcomm.pow_left _
  have hright : Commute ((1 - G) ^ (k - gHatTypeWeight τ)) (1 - G) :=
    (Commute.refl (1 - G)).pow_left _
  unfold gHatTypeOperator
  exact hleft.mul_left hright

/-- The truncated type sum commutes with the base operator `G`. -/
lemma truncatedTypeSums_commute_base
    (G : MIPStarRE.Quantum.Op ι) (d prefixLen : ℕ)
    {tailLen : ℕ} (τtail : GHatType tailLen) :
    Commute (truncatedTypeSums G d prefixLen τtail) G := by
  unfold truncatedTypeSums
  refine Commute.sum_left Finset.univ _ G ?_
  intro τprefix _
  by_cases h : d + 1 ≤ gHatTypeWeight τprefix + gHatTypeWeight τtail
  · simpa [h] using gHatTypeOperator_commute_base G τprefix
  · simp [h]

/-- The truncated type sum commutes with the complementary base operator `1 - G`. -/
lemma truncatedTypeSums_commute_one_sub_base
    (G : MIPStarRE.Quantum.Op ι) (d prefixLen : ℕ)
    {tailLen : ℕ} (τtail : GHatType tailLen) :
    Commute (truncatedTypeSums G d prefixLen τtail) (1 - G) := by
  unfold truncatedTypeSums
  refine Commute.sum_left Finset.univ _ (1 - G) ?_
  intro τprefix _
  by_cases h : d + 1 ≤ gHatTypeWeight τprefix + gHatTypeWeight τtail
  · simpa [h] using gHatTypeOperator_commute_one_sub_base G τprefix
  · simp [h]





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

/-- `fromHToGRecurrenceWeight` commutes with the averaged complete operator `G`. -/
lemma fromHToGRecurrenceWeight_commute_base
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (prefixLen : ℕ)
    {tailLen : ℕ} (τtail : GHatType tailLen) :
    Commute (fromHToGRecurrenceWeight params family prefixLen τtail)
      family.averagedSubMeas.total := by
  exact truncatedTypeSums_commute_base family.averagedSubMeas.total params.d prefixLen τtail

/-- `fromHToGRecurrenceWeight` commutes with `I - G`. -/
lemma fromHToGRecurrenceWeight_commute_one_sub_base
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (prefixLen : ℕ)
    {tailLen : ℕ} (τtail : GHatType tailLen) :
    Commute (fromHToGRecurrenceWeight params family prefixLen τtail)
      (1 - family.averagedSubMeas.total) := by
  exact truncatedTypeSums_commute_one_sub_base
    family.averagedSubMeas.total params.d prefixLen τtail



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







/-- If `A` is PSD and `B ≤ C`, then the corresponding bipartite scalar
expectations with left/right tensor placement are monotone in the right factor. -/
lemma fromHToG_ev_leftTensor_rightTensor_mono_right_of_nonneg_left
    (ψbi : QuantumState (ι × ι))
    {A B C : MIPStarRE.Quantum.Op ι}
    (hA : 0 ≤ A) (hBC : B ≤ C) :
    ev ψbi (leftTensor (ι₂ := ι) A * rightTensor (ι₁ := ι) B) ≤
      ev ψbi (leftTensor (ι₂ := ι) A * rightTensor (ι₁ := ι) C) := by
  apply ev_mono ψbi _ _
  rw [leftTensor_mul_rightTensor_eq_opTensor, leftTensor_mul_rightTensor_eq_opTensor]
  exact MIPStarRE.LDT.opTensor_mono_right hA hBC



/-- Paper `eq:S-sandwich` for the complete branch average `G`. -/
lemma fromHToGRecurrenceWeight_sandwich_base_le
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (prefixLen : ℕ) {tailLen : ℕ} (τtail : GHatType tailLen) :
    let S := fromHToGRecurrenceWeight params family prefixLen τtail
    S * family.averagedSubMeas.total * S ≤ family.averagedSubMeas.total := by
  dsimp
  exact psd_contraction_comm_sandwich_le
    (fromHToGRecurrenceWeight_nonneg params family prefixLen τtail)
    (fromHToGRecurrenceWeight_le_one params family prefixLen τtail)
    family.averagedSubMeas.total_nonneg
    (fromHToGRecurrenceWeight_commute_base params family prefixLen τtail)

/-- Paper `eq:S-sandwich` for the incomplete branch average `I - G`. -/
lemma fromHToGRecurrenceWeight_sandwich_one_sub_base_le
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (prefixLen : ℕ) {tailLen : ℕ} (τtail : GHatType tailLen) :
    let S := fromHToGRecurrenceWeight params family prefixLen τtail
    S * (1 - family.averagedSubMeas.total) * S ≤ 1 - family.averagedSubMeas.total := by
  dsimp
  exact psd_contraction_comm_sandwich_le
    (fromHToGRecurrenceWeight_nonneg params family prefixLen τtail)
    (fromHToGRecurrenceWeight_le_one params family prefixLen τtail)
    (sub_nonneg.mpr family.averagedSubMeas.total_le_one)
    (fromHToGRecurrenceWeight_commute_one_sub_base params family prefixLen τtail)

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

end LIDT

open LIDT
/-!
# Section 12 pasting: from-H-to-G S U S context-average bounds

Sandwich-sum identities and the `S U S` context-average bound used in the
second half-sandwich and final move-right Cauchy--Schwarz steps.
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in

theorem solution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters) [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (ψbi : _root_.LIDT.MIPStarRE.LDT.QuantumState (ι × ι)) (hnorm : ψbi.IsNormalized)
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    (hcomplete : _root_.LIDT.MIPStarRE.LDT.averageOperatorOverDistribution (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params))
      (fun x => (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family x).total) =
        family.averagedSubMeas.total)
    (hincomplete : _root_.LIDT.MIPStarRE.LDT.averageOperatorOverDistribution (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params))
      (fun x => (_root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartSubMeas params family x).total) =
        1 - family.averagedSubMeas.total)
    (ℓ n : ℕ) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n)) (fun q =>
      ∑ ogs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n,
        let S := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight params family ℓ
          (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit ogs.1.isSome (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType ogs.2))
        let U := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ogs.1
        let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 ogs.2
        _root_.LIDT.MIPStarRE.LDT.ev ψbi
          ((_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (S * U)) *
            (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (S * U))ᴴ)) ≤ 1 := by
  classical
  let F : Bool → _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType n → _root_.LIDT.MIPStarRE.LDT.Fq params → _root_.LIDT.MIPStarRE.LDT.PointTuple params n → _root_.LIDT.MIPStarRE.LDT.Error := fun b τ x xs =>
    ∑ g ∈ (Finset.univ : Finset (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params)) with g.isSome = b,
      ∑ gs ∈ (Finset.univ : Finset (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n)) with
          _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType gs = τ,
        let S := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight params family ℓ (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit b τ)
        let U := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family x).outcome g
        let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n xs gs
        _root_.LIDT.MIPStarRE.LDT.ev ψbi ((_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (S * U)) *
          (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (S * U))ᴴ)
  have hsplit :
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n)) (fun q =>
        ∑ ogs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n,
          let S := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight params family ℓ
            (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit ogs.1.isSome (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType ogs.2))
          let U := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ogs.1
          let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 ogs.2
          _root_.LIDT.MIPStarRE.LDT.ev ψbi ((_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (S * U)) *
            (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (S * U))ᴴ)) =
      ∑ b : Bool, ∑ τ : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType n,
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params)) (fun x =>
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params n)) (fun xs => F b τ x xs)) := by
    calc
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.PointTuple params n)) (fun q =>
        ∑ ogs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n,
          let S := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight params family ℓ
            (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit ogs.1.isSome (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType ogs.2))
          let U := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ogs.1
          let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n q.2 ogs.2
          _root_.LIDT.MIPStarRE.LDT.ev ψbi ((_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (S * U)) *
            (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (S * U))ᴴ))
        = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params)) (fun x =>
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params n)) (fun xs =>
          ∑ ogs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n,
            let S := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight params family ℓ
              (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit ogs.1.isSome (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType ogs.2))
            let U := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family x).outcome ogs.1
            let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n xs ogs.2
            _root_.LIDT.MIPStarRE.LDT.ev ψbi ((_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (S * U)) *
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (S * U))ᴴ))) := by
            simpa using (_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_prod (α := _root_.LIDT.MIPStarRE.LDT.Fq params) (β := _root_.LIDT.MIPStarRE.LDT.PointTuple params n)
              (f := fun x xs =>
                ∑ ogs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n,
                  let S := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight params family ℓ
                    (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit ogs.1.isSome (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType ogs.2))
                  let U := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family x).outcome ogs.1
                  let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n xs ogs.2
                  _root_.LIDT.MIPStarRE.LDT.ev ψbi ((_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (S * U)) *
                    (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (S * U))ᴴ)))
      _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params)) (fun x =>
            _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params n)) (fun xs =>
              ∑ b : Bool, ∑ τ : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType n,
                F b τ x xs)) := by
              refine _root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ ?_
              intro x
              refine _root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ ?_
              intro xs
              rw [(_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_sum_product (fun g gs =>
                let S := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight params family ℓ
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit g.isSome (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType gs))
                let U := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family x).outcome g
                let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n xs gs
                _root_.LIDT.MIPStarRE.LDT.ev ψbi ((_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (S * U)) *
                  (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (S * U))ᴴ))).symm]
              symm
              exact _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_bool_type_filtered_outcome_sum params
                (fun b τ g gs =>
                  let S := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight params family ℓ (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit b τ)
                  let U := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family x).outcome g
                  let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n xs gs
                  _root_.LIDT.MIPStarRE.LDT.ev ψbi ((_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (S * U)) *
                    (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (S * U))ᴴ))
      _ = ∑ b : Bool, ∑ τ : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType n,
            _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params)) (fun x =>
              _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params n)) (fun xs => F b τ x xs)) := by
              symm
              exact _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_sum_2_avgOver_2
                (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params))
                (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params n)) F
  let branchRhs : Bool → _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType n → _root_.LIDT.MIPStarRE.LDT.Error := fun b τ =>
    _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (_root_.LIDT.MIPStarRE.LDT.Pasting.averagedSandwichByTypeSubMeas params family n τ).total *
      _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
        (if b then family.averagedSubMeas.total else 1 - family.averagedSubMeas.total))
  have hbranchSum : ∀ b : Bool,
      ∑ τ : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType n,
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params)) (fun x =>
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params n)) (fun xs => F b τ x xs)) ≤
      ∑ τ : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType n, branchRhs b τ := by
    intro b
    refine Finset.sum_le_sum ?_
    intro τ _hτ
    let S := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight params family ℓ (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit b τ)
    let Aτ := (_root_.LIDT.MIPStarRE.LDT.Pasting.averagedSandwichByTypeSubMeas params family n τ).total
    change _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params)) (fun x =>
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params n)) (fun xs => F b τ x xs)) ≤
      branchRhs b τ
    have hrew :
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params)) (fun x =>
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params n)) (fun xs => F b τ x xs)) =
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params)) (fun x =>
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params n)) (fun xs =>
            ∑ g ∈ (Finset.univ : Finset (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params)) with g.isSome = b,
              ∑ gs ∈ (Finset.univ : Finset (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n)) with
                  _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType gs = τ,
                let U := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family x).outcome g
                let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n xs gs
                _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (T * Tᴴ) *
                  _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (S * U * S)))) := by
      refine _root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ ?_
      intro x
      refine _root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ ?_
      intro xs
      dsimp [F, S]
      refine Finset.sum_congr rfl ?_
      intro g _hg
      refine Finset.sum_congr rfl ?_
      intro gs _hgs
      let U := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family x).outcome g
      let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n xs gs
      have hUherm : Uᴴ = U := by
        simpa [U] using _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_gHatIdxMeas_outcome_isHermitian params family x g
      have hUproj : U * U = U := by
        simpa [U] using _root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas_proj params family x g
      have hSherm : Sᴴ = S :=
        _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight_isHermitian params family ℓ (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit b τ)
      calc
        _root_.LIDT.MIPStarRE.LDT.ev ψbi ((_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (S * U)) *
            (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (S * U))ᴴ)
          = _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (T * Tᴴ) *
              _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((S * U) * (Uᴴ * Sᴴ))) := by
              rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor]
              rw [_root_.LIDT.MIPStarRE.LDT.conjTranspose_opTensor, _root_.LIDT.MIPStarRE.LDT.opTensor_mul, Matrix.conjTranspose_mul]
              rw [show _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (T * Tᴴ) *
                  _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((S * U) * (Uᴴ * Sᴴ)) =
                    _root_.LIDT.MIPStarRE.LDT.opTensor (T * Tᴴ) ((S * U) * (Uᴴ * Sᴴ)) by
                rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor]]
        _ = _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (T * Tᴴ) *
              _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (S * U * S)) := by
              have hright : (S * U) * (Uᴴ * Sᴴ) = S * U * S := by
                calc
                  (S * U) * (Uᴴ * Sᴴ) = S * U * (U * S) := by rw [hUherm, hSherm]
                  _ = S * (U * U) * S := by simp [mul_assoc]
                  _ = S * U * S := by rw [hUproj]
              simp [hright]
    rw [hrew]
    calc
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params)) (fun x =>
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params n)) (fun xs =>
          ∑ g ∈ (Finset.univ : Finset (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params)) with g.isSome = b,
            ∑ gs ∈ (Finset.univ : Finset (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n)) with
                _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType gs = τ,
              let U := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family x).outcome g
              let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n xs gs
              _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (T * Tᴴ) *
                _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (S * U * S))))
        = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params)) (fun x =>
            _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params n)) (fun xs =>
              ∑ gs ∈ (Finset.univ : Finset (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n)) with
                  _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType gs = τ,
                let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n xs gs
                let B := if b then (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family x).total
                  else (_root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartSubMeas params family x).total
                _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (T * Tᴴ) *
                  _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (S * B * S)))) := by
              refine _root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ ?_
              intro x
              refine _root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ ?_
              intro xs
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl ?_
              intro gs _hgs
              simpa [S] using
                (_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_ev_sum_isSome_sandwich_weight params ψbi family x b
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n xs gs *
                    (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n xs gs)ᴴ) S)
      _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params)) (fun x =>
            _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) Aτ *
              _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
                (S * (if b then (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family x).total
                  else (_root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartSubMeas params family x).total) * S))) := by
              refine _root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ ?_
              intro x
              simpa [Aτ, S, _root_.LIDT.MIPStarRE.LDT.Pasting.gHatSandwichFamily] using
                (_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_avgOver_tail_type_ev_sandwich params ψbi family n τ
                  (S * (if b then (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family x).total
                    else (_root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartSubMeas params family x).total) * S))
      _ = _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) Aτ *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
              (S * (if b then family.averagedSubMeas.total
                else 1 - family.averagedSubMeas.total) * S)) := by
              simpa [Aτ, S] using
                (_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_avgOver_head_branch_ev_sandwich params ψbi family
                  hcomplete hincomplete b Aτ S)
      _ ≤ _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) Aτ *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
              (if b then family.averagedSubMeas.total else 1 - family.averagedSubMeas.total)) := by
              have hAτ_nonneg : 0 ≤ Aτ := by
                simpa [Aτ] using
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.averagedSandwichByTypeSubMeas params family n τ).total_nonneg
              cases b
              · simpa [S] using
                  _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_ev_leftTensor_rightTensor_mono_right_of_nonneg_left ψbi hAτ_nonneg
                    (_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight_sandwich_one_sub_base_le params family ℓ
                      (τtail := _root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit false τ))
              · simpa [S] using
                  _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_ev_leftTensor_rightTensor_mono_right_of_nonneg_left ψbi hAτ_nonneg
                    (_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight_sandwich_base_le params family ℓ
                      (τtail := _root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit true τ))
      _ = branchRhs b τ := by rfl
  rw [hsplit]
  calc
    ∑ b : Bool, ∑ τ : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType n,
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params)) (fun x =>
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params n)) (fun xs => F b τ x xs))
      ≤ ∑ b : Bool, ∑ τ : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType n, branchRhs b τ := by
            refine Finset.sum_le_sum ?_
            intro b _hb
            exact hbranchSum b
    _ = ∑ τ : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType n, ∑ b : Bool, branchRhs b τ := by
            rw [Finset.sum_comm]
    _ = ∑ τ : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType n,
          _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
            (_root_.LIDT.MIPStarRE.LDT.Pasting.averagedSandwichByTypeSubMeas params family n τ).total *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
              (family.averagedSubMeas.total + (1 - family.averagedSubMeas.total))) := by
            refine Finset.sum_congr rfl ?_
            intro τ _hτ
            rw [Fintype.sum_bool]
            dsimp [branchRhs]
            rw [← _root_.LIDT.MIPStarRE.LDT.ev_add]
            apply congrArg (_root_.LIDT.MIPStarRE.LDT.ev ψbi)
            calc
              _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                (_root_.LIDT.MIPStarRE.LDT.Pasting.averagedSandwichByTypeSubMeas params family n τ).total *
                  _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) family.averagedSubMeas.total +
                _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.averagedSandwichByTypeSubMeas params family n τ).total *
                  _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (1 - family.averagedSubMeas.total)
                = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                    (_root_.LIDT.MIPStarRE.LDT.Pasting.averagedSandwichByTypeSubMeas params family n τ).total *
                    (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) family.averagedSubMeas.total +
                      _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (1 - family.averagedSubMeas.total)) := by
                        rw [← mul_add]
              _ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                    (_root_.LIDT.MIPStarRE.LDT.Pasting.averagedSandwichByTypeSubMeas params family n τ).total *
                    _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
                      (family.averagedSubMeas.total + (1 - family.averagedSubMeas.total)) := by
                        rw [_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_rightTensor_add]
    _ = ∑ τ : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType n,
          _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
            (_root_.LIDT.MIPStarRE.LDT.Pasting.averagedSandwichByTypeSubMeas params family n τ).total) := by
            refine Finset.sum_congr rfl ?_
            intro τ _hτ
            have hone : family.averagedSubMeas.total +
                (1 - family.averagedSubMeas.total) = (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) := by
              simp
            rw [hone, _root_.LIDT.MIPStarRE.LDT.rightTensor_one, mul_one]
    _ = _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
          (∑ τ : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType n,
            (_root_.LIDT.MIPStarRE.LDT.Pasting.averagedSandwichByTypeSubMeas params family n τ).total)) := by
            rw [← _root_.LIDT.MIPStarRE.LDT.ev_sum]
            rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_finset_sum]
    _ = _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι)) := by
          rw [_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_sum_averagedSandwichByType_total_eq_one params family n]
    _ = 1 := by simpa [_root_.LIDT.MIPStarRE.LDT.leftTensor] using _root_.LIDT.MIPStarRE.LDT.ev_one_of_isNormalized ψbi hnorm
