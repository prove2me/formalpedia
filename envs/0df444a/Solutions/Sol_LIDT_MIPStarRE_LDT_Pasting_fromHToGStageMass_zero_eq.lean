-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.fromHToGStageMass_zero_eq
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T15:43:57.2438+00:00
-- url     : https://prove2.me/submissions/4f1b93e5-6c15-49b0-9305-6a7a6c4ad8b2

-- Generated proof for MIPStarRE.LDT.Pasting.fromHToGStageMass_zero_eq.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_Core_BernoulliTail
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_fromHToG_averagedEligibleSandwich_total_eq_type_sum

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











/-- Tensor placement collapses to the left factor when the right recurrence weight
is the stage-`0` eligibility indicator. -/
lemma fromHToG_leftTensor_mul_rightTensor_indicator
    (A : MIPStarRE.Quantum.Op ι) (p : Prop) [Decidable p] :
    leftTensor (ι₂ := ι) A * rightTensor (ι₁ := ι)
        (if p then 1 else 0 : MIPStarRE.Quantum.Op ι) =
      leftTensor (ι₂ := ι) (if p then A else 0) := by
  by_cases hp : p <;> simp [hp, leftTensor, rightTensor]

















end MIPStarRE.LDT.Pasting

end

/- Source helpers from MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/Core/BernoulliTail.lean. -/
/-!
# Section 12 pasting: Bernoulli tail polynomial combinatorics

Finset re-indexing and cardinality-grouping lemmas for the Bernoulli-tail
operator endpoint of the `fromHToG` recurrence.
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]













/-- At prefix length zero, the recurrence weight is exactly the eligibility
indicator for the remaining type: the empty prefix contributes the identity when
`|τtail| ≥ d + 1`, and contributes zero otherwise. -/
lemma fromHToG_truncatedTypeSums_zero_eq_indicator
    (G : MIPStarRE.Quantum.Op ι) (d : ℕ) {tailLen : ℕ} (τtail : GHatType tailLen) :
    truncatedTypeSums G d 0 τtail =
      if d + 1 ≤ gHatTypeWeight τtail then 1 else 0 := by
  simp [truncatedTypeSums, gHatTypeOperator, gHatTypeWeight]

end MIPStarRE.LDT.Pasting

end

end LIDT

open LIDT
/-!
# Section 12 pasting: from-H-to-G stage-mass bookkeeping

Stage-`0` identification, terminal identification, adjacent-stage split, and
telescoping lemmas that connect the Lean recurrence stages to the paper scalars.
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]













-- This declaration expands a finite operator average into the corresponding
-- scalar trace average; the displayed statement is less readable after writing
-- the fully expanded finite-sum target as an intermediate `suffices`.


-- This declaration is the right-register analogue of the preceding finite-sum
-- expansion; spelling out the simplified scalar target obscures the average
-- identity being proved.

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters)
    [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (strategy : _root_.LIDT.MIPStarRE.LDT.SymStrat params.next ι)
    (ψbi : _root_.LIDT.MIPStarRE.LDT.QuantumState (ι × ι))
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι) (k : ℕ) :
    _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGStageMass params ψbi family k 0 =
      _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGAllOutcomesMass params strategy ψbi family k := by
  classical
  have htotal := _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_averagedEligibleSandwich_total_eq_type_sum params family k
  unfold _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGStageMass _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGTailStageMass _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGAllOutcomesMass _root_.LIDT.MIPStarRE.LDT.subMeasMass
  simp only [Nat.sub_zero,
    _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGTailStageFamily, _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight, _root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft,
    _root_.LIDT.MIPStarRE.LDT.Pasting.allOutcomesExpansionFamily, _root_.LIDT.MIPStarRE.LDT.Pasting.pastedMeasurementTotal, _root_.LIDT.MIPStarRE.LDT.constSubMeasFamily,
    _root_.LIDT.MIPStarRE.LDT.mkLeftPlacedSubMeas_total]
  change (∑ τ : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType k,
      _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
        (_root_.LIDT.MIPStarRE.LDT.Pasting.averagedSandwichByTypeSubMeas params family k τ).total *
          _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
            (_root_.LIDT.MIPStarRE.LDT.Pasting.truncatedTypeSums family.averagedSubMeas.total params.d 0 τ))) =
    _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (_root_.LIDT.MIPStarRE.LDT.Pasting.averagedEligibleSandwichSubMeas params family k).total)
  rw [htotal]
  simp only [_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_truncatedTypeSums_zero_eq_indicator]
  calc
    (∑ τ : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType k,
        _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
          (_root_.LIDT.MIPStarRE.LDT.Pasting.averagedSandwichByTypeSubMeas params family k τ).total *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
              (if params.d + 1 ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight τ then 1 else 0 :
                _root_.LIDT.MIPStarRE.Quantum.Op ι)))
      = ∑ τ : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType k,
        _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
          (if params.d + 1 ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight τ then
            (_root_.LIDT.MIPStarRE.LDT.Pasting.averagedSandwichByTypeSubMeas params family k τ).total
          else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro τ _
          rw [_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_leftTensor_mul_rightTensor_indicator]
    _
      = _root_.LIDT.MIPStarRE.LDT.ev ψbi (∑ τ : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType k,
          _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
            (if params.d + 1 ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight τ then
              (_root_.LIDT.MIPStarRE.LDT.Pasting.averagedSandwichByTypeSubMeas params family k τ).total
            else 0)) := by
          exact (_root_.LIDT.MIPStarRE.LDT.ev_sum ψbi (fun τ : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType k =>
            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
              (if params.d + 1 ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight τ then
                (_root_.LIDT.MIPStarRE.LDT.Pasting.averagedSandwichByTypeSubMeas params family k τ).total
              else 0))).symm
    _ = _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
        (∑ τ : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType k,
          if params.d + 1 ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight τ then
            (_root_.LIDT.MIPStarRE.LDT.Pasting.averagedSandwichByTypeSubMeas params family k τ).total
          else 0)) := by
          simpa using congrArg (_root_.LIDT.MIPStarRE.LDT.ev ψbi)
            (_root_.LIDT.MIPStarRE.LDT.leftTensor_finset_sum (ι₂ := ι)
              (Finset.univ : Finset (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatType k))
              (fun τ : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType k =>
                if params.d + 1 ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight τ then
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.averagedSandwichByTypeSubMeas params family k τ).total
                else 0))
