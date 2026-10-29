-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.gHatSandwich_sum_last_eq_prefix
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T16:24:54.183782+00:00
-- url     : https://prove2.me/submissions/dbb415c9-cc4b-4fea-a70d-a482f0ecf52f

-- Generated proof for MIPStarRE.LDT.Pasting.gHatSandwich_sum_last_eq_prefix.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_Endpoint
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_EndpointEquivs
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_gHatHalfProduct_prefix_mul_last

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

/- Source helpers from MIPStarRE/LDT/Pasting/ComparisonLemmas/LdSandwichLineOnePoint/PrefixMoved.lean. -/
/-!
# Section 12 pasting: line one-point transport — prefix moved lemmas

Internal helper module; part of the file-split for `#1127`.

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















/-- Split the ordered half-product into its first `n` coordinates and the last slice. -/
lemma gHatHalfProductOutcomeOperator_prefix_last
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    ∀ n (xs : PointTuple params (n + 1)) (gs : GHatTupleOutcome params (n + 1)),
      gHatHalfProductOutcomeOperator params family (n + 1) xs gs =
        gHatHalfProductOutcomeOperator params family n
            (fun j => xs ⟨j.1, by omega⟩)
            (fun j => gs ⟨j.1, by omega⟩) *
          (gHatIdxMeas params family (xs ⟨n, Nat.lt_succ_self n⟩)).outcome
            (gs ⟨n, Nat.lt_succ_self n⟩)
  | 0, xs, gs => by
      simp [gHatHalfProductOutcomeOperator]
  | n + 1, xs, gs => by
      simpa using gHatHalfProduct_prefix_mul_last params family n xs gs







end MIPStarRE.LDT.Pasting

end

end LIDT

open LIDT
/-!
# Section 12 pasting: line one-point transport — prefix moved lemmas

Internal helper module; part of the file-split for `#1127`.

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
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters)
    [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    (n : ℕ) (xs : _root_.LIDT.MIPStarRE.LDT.PointTuple params (n + 1))
    (gsPrefix : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n) :
    (∑ g : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params,
      let half := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family (n + 1) xs
        ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleOutcomePrefixLastEquiv params n).symm (gsPrefix, g))
      half * halfᴴ) =
      _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n
        (fun j => xs ⟨j.1, by omega⟩) gsPrefix *
        (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n
          (fun j => xs ⟨j.1, by omega⟩) gsPrefix)ᴴ := by
  let P : _root_.LIDT.MIPStarRE.Quantum.Op ι :=
    _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n
      (fun j => xs ⟨j.1, by omega⟩) gsPrefix
  let G : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params → _root_.LIDT.MIPStarRE.Quantum.Op ι := fun g =>
    (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family (xs ⟨n, Nat.lt_succ_self n⟩)).outcome g
  have hsumG : (∑ g : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params, G g) = 1 := by
    dsimp [G]
    rw [(_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family (xs ⟨n, Nat.lt_succ_self n⟩)).sum_eq_total]
    simp [_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas, _root_.LIDT.MIPStarRE.LDT.completeSubMeas]
  have hsumGG : (∑ g : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params, G g * (G g)ᴴ) = 1 := by
    calc
      (∑ g : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params, G g * (G g)ᴴ)
          = ∑ g : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params, G g := by
            refine Finset.sum_congr rfl ?_
            intro g _hg
            have hherm : (G g)ᴴ = G g := by
              simpa [G] using
                (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family (xs ⟨n, Nat.lt_succ_self n⟩)).outcome_hermitian g
            have hproj : G g * G g = G g := by
              simpa [G] using
                _root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas_proj params family (xs ⟨n, Nat.lt_succ_self n⟩) g
            simp [hherm, hproj]
      _ = 1 := hsumG
  have hinner : (∑ g : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params, (P * G g) * (P * G g)ᴴ) = P * Pᴴ := by
    calc
      (∑ g : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params, (P * G g) * (P * G g)ᴴ)
          = ∑ g : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params, P * (G g * (G g)ᴴ) * Pᴴ := by
            refine Finset.sum_congr rfl ?_
            intro g _hg
            simp [Matrix.conjTranspose_mul, mul_assoc]
      _ = P * (∑ g : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params, G g * (G g)ᴴ) * Pᴴ := by
            rw [← Finset.sum_mul, ← Matrix.mul_sum]
      _ = P * Pᴴ := by
            simp [hsumGG]
  calc
    (∑ g : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params,
      let half := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family (n + 1) xs
        ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleOutcomePrefixLastEquiv params n).symm (gsPrefix, g))
      half * halfᴴ)
        = ∑ g : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params, (P * G g) * (P * G g)ᴴ := by
          refine Finset.sum_congr rfl ?_
          intro g _hg
          simp [P, G, _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleOutcomePrefixLastEquiv,
            _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator_prefix_last]
    _ = P * Pᴴ := hinner
    _ = _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n
          (fun j => xs ⟨j.1, by omega⟩) gsPrefix *
        (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n
          (fun j => xs ⟨j.1, by omega⟩) gsPrefix)ᴴ := by
        rfl
