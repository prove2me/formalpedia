-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.fromHToG_avgOver_tail_type_ev
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T15:34:17.868907+00:00
-- url     : https://prove2.me/submissions/be6ce952-3d86-4f94-b107-e5bf3abb788f

-- Generated proof for MIPStarRE.LDT.Pasting.fromHToG_avgOver_tail_type_ev.
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

/- Source helpers from MIPStarRE/LDT/Basic/TensorPlacement.lean. -/
/-!
# Tensor-placement helper lemmas and sandwich tensor estimates

Tensor-sum commutation, positivity/boundedness preservation,
factoring lemmas, and sandwich-residual estimates used in
the main induction step and polynomial-agreement arguments.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT

/-! ### Tensor-placement helper lemmas -/























/-- A complex scalar on the left register factors out of a bipartite tensor product.

This is the tensor-placement version of bilinearity of `opTensor`: placing
`c • A` on the left and multiplying by the right placement of `B` equals the
same scalar multiplying `leftTensor A * rightTensor B`. -/
theorem leftTensor_mul_rightTensor_smul_left
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (c : Error) (A : MIPStarRE.Quantum.Op ι₁) (B : MIPStarRE.Quantum.Op ι₂) :
    leftTensor (ι₂ := ι₂) ((c : ℂ) • A) * rightTensor (ι₁ := ι₁) B =
      (c : ℂ) • (leftTensor (ι₂ := ι₂) A * rightTensor (ι₁ := ι₁) B) := by
  rw [leftTensor_mul_rightTensor_eq_opTensor, leftTensor_mul_rightTensor_eq_opTensor]
  simpa [opTensor] using Matrix.smul_kronecker (c : ℂ) A B



/-- A real scalar on the left register factors out of a bipartite tensor product.

This restates `leftTensor_mul_rightTensor_smul_left` for the real scalar action
used by `averageOperatorOverDistribution`, coercing the real scalar to `ℂ` on
the tensor product. -/
theorem leftTensor_mul_rightTensor_real_smul_left
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (c : Error) (A : MIPStarRE.Quantum.Op ι₁) (B : MIPStarRE.Quantum.Op ι₂) :
    leftTensor (ι₂ := ι₂) (c • A) * rightTensor (ι₁ := ι₁) B =
      (c : ℂ) • (leftTensor (ι₂ := ι₂) A * rightTensor (ι₁ := ι₁) B) := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact leftTensor_mul_rightTensor_smul_left c A B













namespace SubMeas



end SubMeas

/-! ### Sandwich tensor estimates -/





end MIPStarRE.LDT

end

/- Source helpers from MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/Core/StageMass.lean. -/
/-!
# Section 12 pasting: from-H-to-G stage-mass bookkeeping

Stage-`0` identification, terminal identification, adjacent-stage split, and
telescoping lemmas that connect the Lean recurrence stages to the paper scalars.
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]





/-- Membership in `outcomesByType τ` is the same as having tuple type `τ`. -/
lemma fromHToG_outcomesByType_iff_type_eq
    {params : Parameters} [FieldModel params.q] {k : ℕ}
    (gs : GHatTupleOutcome params k) (τ : GHatType k) :
    gs ∈ outcomesByType τ ↔ gHatTupleType gs = τ := by
  simp [outcomesByType, gHatTupleType, funext_iff]





/-- The per-type averaged sandwich total is the uniform average of the exact-type
fibers of `gHatSandwichFamily`. -/
lemma fromHToG_averagedSandwichByType_total_eq_type_sum
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ) (τ : GHatType k) :
    (averagedSandwichByTypeSubMeas params family k τ).total =
      ∑ xs ∈ (uniformDistribution (PointTuple params k)).support,
        (uniformDistribution (PointTuple params k)).weight xs •
          (∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params k)) with
            gHatTupleType gs = τ,
            (gHatSandwichFamily params family k xs).outcome gs) := by
  classical
  simp only [averagedSandwichByTypeSubMeas, averageIdxSubMeas,
    averageOperatorOverDistribution]
  refine Finset.sum_congr rfl ?_
  intro xs _hxs
  congr 1
  simp [restrictSubMeas, postprocess, fromHToG_outcomesByType_iff_type_eq]

-- This declaration expands a finite operator average into the corresponding
-- scalar trace average; the displayed statement is less readable after writing
-- the fully expanded finite-sum target as an intermediate `suffices`.


-- This declaration is the right-register analogue of the preceding finite-sum
-- expansion; spelling out the simplified scalar target obscures the average
-- identity being proved.
















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

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters) [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (ψbi : _root_.LIDT.MIPStarRE.LDT.QuantumState (ι × ι))
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι) (n : ℕ) (τ : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType n)
    (B : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params n)) (fun xs =>
      ∑ gs ∈ (Finset.univ : Finset (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n)) with
          _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType gs = τ,
        let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n xs gs
        _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (T * Tᴴ) * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) B)) =
      _root_.LIDT.MIPStarRE.LDT.ev ψbi (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
        (_root_.LIDT.MIPStarRE.LDT.Pasting.averagedSandwichByTypeSubMeas params family n τ).total *
          _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) B) := by
  classical
  rw [_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_averagedSandwichByType_total_eq_type_sum params family n τ]
  simp only [_root_.LIDT.MIPStarRE.LDT.avgOver, _root_.LIDT.MIPStarRE.LDT.Pasting.gHatSandwichFamily, ← _root_.LIDT.MIPStarRE.LDT.leftTensor_finset_sum, Finset.sum_mul,
    _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_real_smul_left, Complex.coe_smul, _root_.LIDT.MIPStarRE.LDT.ev_finset_sum]
  apply Finset.sum_congr rfl
  intro xs _hxs
  rw [← _root_.LIDT.MIPStarRE.LDT.ev_finset_sum]
  exact (_root_.LIDT.MIPStarRE.LDT.ev_scale ψbi ((_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params n)).weight xs)
    (∑ i with _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleType i = τ,
      _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
          (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n xs i *
            (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n xs i)ᴴ) *
        _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) B)).symm
