-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.fromHToG_averagedSandwichByTypeSubMeas_zero_total_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T15:29:29.235083+00:00
-- url     : https://prove2.me/submissions/07ba98d9-a0ca-4c63-9bfd-82dbfab9dde8

-- Generated proof for MIPStarRE.LDT.Pasting.fromHToG_averagedSandwichByTypeSubMeas_zero_total_eq_one.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_averageOperatorOverDistribution_const_of_isProbability

namespace LIDT.MIPStarRE.LDT.Pasting
end LIDT.MIPStarRE.LDT.Pasting

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

lemma fromHToG_averageOperator_uniform_const_one
    (α : Type*) [Fintype α] [DecidableEq α] [Nonempty α] :
    averageOperatorOverDistribution (uniformDistribution α)
      (fun _ : α => (1 : MIPStarRE.Quantum.Op ι)) = 1 := by
  exact averageOperatorOverDistribution_const_of_isProbability
    (uniformDistribution α) (uniformDistribution_isProbability α) 1





/-- A zero-length type restriction of the sandwiched family has total identity.
This isolates the `tailLen = 0` collapse of `outcomesByType`, `restrictSubMeas`,
and the empty half-sandwich product. -/
lemma fromHToG_emptyRestrictedSandwichTotal_eq_one
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (xs : PointTuple params 0) (τ : GHatType 0) :
    (postprocess
      (@restrictSubMeas ι _ _ (GHatTupleOutcome params 0) _
        (gHatSandwichFamily params family 0 xs)
        (fun gs => gs ∈ outcomesByType τ)
        (Classical.decPred (fun gs => gs ∈ outcomesByType τ)))
      (fun _ => ())).total = 1 := by
  simp only [restrictSubMeas, outcomesByType, IsEmpty.forall_iff, Set.ofPred_true,
    Set.mem_univ, ↓reduceIte, gHatSandwichFamily, gHatHalfProductOutcomeOperator,
    Matrix.conjTranspose_one, mul_one, gHatHalfProductTotalOperator, Finset.univ_unique,
    Finset.filter_true, Finset.sum_const, Finset.card_singleton, one_smul, postprocess_total]





















end MIPStarRE.LDT.Pasting

end

end LIDT

open LIDT
/-!
# Section 12 pasting: operator averages and projective submeasurement lemmas

Averages over uniform distributions, tensor placement identities, and
projective submeasurement algebraic lemmas for the `fromHToG` reduction.
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters) [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι) (τ : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType 0) :
    (_root_.LIDT.MIPStarRE.LDT.Pasting.averagedSandwichByTypeSubMeas params family 0 τ).total = 1 := by
  simp only [_root_.LIDT.MIPStarRE.LDT.Pasting.averagedSandwichByTypeSubMeas, _root_.LIDT.MIPStarRE.LDT.averageIdxSubMeas]
  rw [show (fun xs : _root_.LIDT.MIPStarRE.LDT.PointTuple params 0 =>
      (_root_.LIDT.MIPStarRE.LDT.postprocess
        (@_root_.LIDT.MIPStarRE.LDT.Pasting.restrictSubMeas ι _ _ (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params 0) _
          (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSandwichFamily params family 0 xs)
          (fun gs => gs ∈ _root_.LIDT.MIPStarRE.LDT.Pasting.outcomesByType τ)
          (Classical.decPred (fun gs => gs ∈ _root_.LIDT.MIPStarRE.LDT.Pasting.outcomesByType τ)))
        (fun _ => ())).total) =
      (fun _ : _root_.LIDT.MIPStarRE.LDT.PointTuple params 0 => (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι)) by
    funext xs
    exact _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_emptyRestrictedSandwichTotal_eq_one params family xs τ]
  exact _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_averageOperator_uniform_const_one (_root_.LIDT.MIPStarRE.LDT.PointTuple params 0)
