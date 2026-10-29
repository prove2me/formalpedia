-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.fromHToG_gHatHalfProduct_reverse_eq_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T15:50:55.983372+00:00
-- url     : https://prove2.me/submissions/45f12d81-fd8e-43f0-98c5-0fbba3d03768

-- Generated proof for MIPStarRE.LDT.Pasting.fromHToG_gHatHalfProduct_reverse_eq_adjoint.
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_fromHToG_gHatHalfProductOutcomeOperator_snoc

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



























end MIPStarRE.LDT.Pasting

end

end LIDT

open LIDT
/-!
# Section 12 pasting: from-H-to-G move lemmas

Tensor, positivity, and Cauchy--Schwarz helper lemmas for the adjacent paper chain.
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
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι) :
    ∀ (n : ℕ) (xs : _root_.LIDT.MIPStarRE.LDT.PointTuple params n) (gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n),
      _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n
          ((_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGPointTupleReverseEquiv params n) xs)
          ((_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGGHatTupleOutcomeReverseEquiv params n) gs) =
        (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n xs gs)ᴴ
  | 0, _xs, _gs => by
      simp [_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator]
  | n + 1, xs, gs => by
      refine Fin.snocCases ?_ xs
      intro xs x
      refine Fin.snocCases ?_ gs
      intro gs g
      have hheadx : ((_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGPointTupleReverseEquiv params (n + 1)) (Fin.snoc xs x)) 0 = x := by
        change Fin.snoc (α := fun _ : Fin (n + 1) => _root_.LIDT.MIPStarRE.LDT.Fq params) xs x
          (Fin.rev 0) = x
        rw [Fin.rev_zero]
        simp
      have hheadg :
          ((_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGGHatTupleOutcomeReverseEquiv params (n + 1)) (Fin.snoc gs g)) 0 = g := by
        change Fin.snoc (α := fun _ : Fin (n + 1) => _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params) gs g
          (Fin.rev 0) = g
        rw [Fin.rev_zero]
        simp
      have htailx :
          _root_.LIDT.MIPStarRE.LDT.Pasting.pointTupleTail ((_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGPointTupleReverseEquiv params (n + 1)) (Fin.snoc xs x)) =
            (_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGPointTupleReverseEquiv params n) xs := by
        funext i
        change Fin.snoc (α := fun _ : Fin (n + 1) => _root_.LIDT.MIPStarRE.LDT.Fq params) xs x
          (i.succ.rev) = xs i.rev
        rw [Fin.rev_succ]
        simp
      have htailg :
          _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleOutcomeTail ((_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGGHatTupleOutcomeReverseEquiv params (n + 1))
            (Fin.snoc gs g)) =
              (_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGGHatTupleOutcomeReverseEquiv params n) gs := by
        funext i
        change Fin.snoc (α := fun _ : Fin (n + 1) => _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params) gs g
          (i.succ.rev) = gs i.rev
        rw [Fin.rev_succ]
        simp
      rw [_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator, hheadx, hheadg, htailx, htailg]
      rw [solution params family n xs gs]
      rw [_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_gHatHalfProductOutcomeOperator_snoc params family n xs x gs g]
      rw [Matrix.conjTranspose_mul, _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_gHatIdxMeas_outcome_isHermitian]
