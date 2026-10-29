-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePoint_prefix_outcomeSum_cauchySchwarz_facts
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T16:24:54.429047+00:00
-- url     : https://prove2.me/submissions/4efb5b88-97a2-4cf3-a592-b5f07f6bfb55

-- Generated proof for MIPStarRE.LDT.Pasting.ldSandwichLineOnePoint_prefix_outcomeSum_cauchySchwarz_facts.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_CSSetup
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_Endpoint
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_EndpointEquivs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_PrefixMoved
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_gHatSandwichFamily_restrict_eval_outcome_some
import Theorems.Thm_LIDT_MIPStarRE_LDT_opTensor_mul_leftTensor

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

/- Source helpers from MIPStarRE/LDT/Pasting/ComparisonLemmas/LdSandwichLineOnePoint/CSSetup.lean. -/
/-!
# Section 12 pasting: line one-point transport — Cauchy-Schwarz setup

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





























































/-- The adjoint-oriented estimate for the paper's `eq:add-in-the-bot` term.

The generic `closenessOfIP*` applications need the adjoint-oriented
$D D^\dagger$ square-distance term that appears in `ld-pasting.tex:980--985`
and is reused at lines `1005--1010`. -/
lemma ldSandwichLineOnePoint_prefix_outcomeSum_cauchySchwarz_adjointRawCore
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    {k i : ℕ} (hi : i < k) (_hi0 : i ≠ 0)
    (facts : LdSandwichLineOnePointAdjointRawCoreBound params strategy family gamma zeta hi) :
    avgOver (uniformDistribution (SandwichedLineQuestion params k))
      (fun q => qSDDCore strategy.state
        (fun gs : GHatTupleOutcome params (i + 1) =>
          (ldSandwichLineOnePointCS_Aord params family hi q gs)ᴴ)
        (fun gs : GHatTupleOutcome params (i + 1) =>
          (ldSandwichLineOnePointCS_Arot params family hi q gs)ᴴ)) ≤
      commuteGHalfSandwichError params gamma zeta (i + 1) := by
  exact facts.bound


end MIPStarRE.LDT.Pasting

end

/- Source helpers from MIPStarRE/LDT/Pasting/ComparisonLemmas/LdSandwichLineOnePoint/OutcomeLemmas.lean. -/
/-!
# Section 12 pasting: line one-point transport — outcome lemmas

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











/-- Outcome expansion for the original-order prefix family at a concrete field value. -/
lemma ldSandwichLineOnePointPrefixOriginalFamily_outcome_some
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k)
    (q : SandwichedLineQuestion params k)
    (a : Fq params) :
    (ldSandwichLineOnePointPrefixOriginalFamily params family hi q).outcome (some a) =
      ∑ gs : GHatTupleOutcome params (i + 1),
        if Option.map (fun g : Polynomial params => g q.1)
            (gs ⟨i, Nat.lt_succ_self i⟩) = some a then
          let half := gHatHalfProductOutcomeOperator params family (i + 1)
            (fun j => q.2 ⟨j.1, by omega⟩) gs
          half * halfᴴ
        else
          0 := by
  simpa [ldSandwichLineOnePointPrefixOriginalFamily] using
    gHatSandwichFamily_restrict_eval_outcome_some
      params family (fun j => q.2 ⟨j.1, by omega⟩)
      ⟨i, Nat.lt_succ_self i⟩ q.1 a

/-- Outcome expansion for the selected-first prefix family at a concrete field value. -/
lemma ldSandwichLineOnePointPrefixMovedFamily_outcome_some
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k)
    (q : SandwichedLineQuestion params k)
    (a : Fq params) :
    (ldSandwichLineOnePointPrefixMovedFamily params family hi q).outcome (some a) =
      ∑ gs : GHatTupleOutcome params (i + 1),
        if Option.map (fun g : Polynomial params => g q.1) (gs 0) = some a then
          let xsTail : PointTuple params i := fun j => q.2 ⟨j.1, by omega⟩
          let xs : PointTuple params (i + 1) := Fin.cons (q.2 ⟨i, hi⟩) xsTail
          let half := gHatHalfProductOutcomeOperator params family (i + 1) xs gs
          half * halfᴴ
        else
          0 := by
  simpa [ldSandwichLineOnePointPrefixMovedFamily] using
    gHatSandwichFamily_restrict_eval_outcome_some
      params family (Fin.cons (q.2 ⟨i, hi⟩) (fun j => q.2 ⟨j.1, by omega⟩))
      0 q.1 a









-- This arithmetic absorption proof expands several nested error estimates from the paper.



end MIPStarRE.LDT.Pasting

end

end LIDT

open LIDT
/-!
# Section 12 pasting: line one-point transport — Cauchy-Schwarz chain

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
    (strategy : _root_.LIDT.MIPStarRE.LDT.SymStrat params.next ι)
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    (gamma zeta : _root_.LIDT.MIPStarRE.LDT.Error)
    {k i : ℕ} (hi : i < k) (hi0 : i ≠ 0)
    (facts : _root_.LIDT.MIPStarRE.LDT.Pasting.LdSandwichLineOnePointAdjointRawCoreBound params strategy family gamma zeta hi) :
    _root_.LIDT.MIPStarRE.LDT.Pasting.LdSandwichLineOnePointCSFacts params strategy family gamma zeta hi := by
  refine ⟨
    _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePoint_prefix_outcomeSum_cauchySchwarz_adjointRawCore
      params strategy family gamma zeta hi hi0 facts,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q
    classical
    calc
      ∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params (i + 1),
          (∑ u : Unit, _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_Cfirst params strategy family hi q gs u)ᴴ *
            (∑ u : Unit, _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_Cfirst params strategy family hi q gs u)
          ≤ ∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params (i + 1),
              _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                (_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_orderedHalf params family hi q gs *
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_orderedHalf params family hi q gs)ᴴ) := by
            refine Finset.sum_le_sum ?_
            intro gs _hgs
            let O : _root_.LIDT.MIPStarRE.Quantum.Op ι :=
              _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_orderedHalf params family hi q gs
            let R : _root_.LIDT.MIPStarRE.Quantum.Op ι :=
              _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_rightComplement params strategy family q gs
            have hRle : Rᴴ * R ≤ 1 := by
              dsimp [R, _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_rightComplement]
              split
              · simp
              · rename_i a _ha
                let B : _root_.LIDT.MIPStarRE.Quantum.Op ι :=
                  ((_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointRightFamily params strategy family k i) q).outcome
                    (some a)
                have hBpos : 0 ≤ B := by
                  simpa [B] using
                    ((_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointRightFamily params strategy family k i) q).outcome_pos
                      (some a)
                have hBle : B ≤ 1 := by
                  simpa [B] using
                    _root_.LIDT.MIPStarRE.LDT.SubMeas.outcome_le_one
                      ((_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointRightFamily params strategy family k i) q)
                      (some a)
                have hRpos : 0 ≤ (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) - B := sub_nonneg.mpr hBle
                have hRle_one : (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) - B ≤ 1 := by
                  simpa [sub_eq_add_neg] using sub_le_self (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) hBpos
                have hRherm : ((1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) - B)ᴴ = 1 - B := by
                  simp [B, _root_.LIDT.MIPStarRE.LDT.SubMeas.outcome_hermitian]
                calc
                  ((1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) - B)ᴴ * (1 - B)
                      = (1 - B) * (1 - B) := by rw [hRherm]
                  _ ≤ 1 - B := _root_.LIDT.MIPStarRE.Quantum.sq_le_self hRpos hRle_one
                  _ ≤ 1 := hRle_one
            have hOpos : 0 ≤ O * Oᴴ := by
              simpa [O] using (Matrix.posSemidef_self_mul_conjTranspose O).nonneg
            calc
              (∑ u : Unit, _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_Cfirst params strategy family hi q gs u)ᴴ *
                  (∑ u : Unit, _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_Cfirst params strategy family hi q gs u)
                  = _root_.LIDT.MIPStarRE.LDT.opTensor (O * Oᴴ) (Rᴴ * R) := by
                    simp [O, R, _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_Cfirst, _root_.LIDT.MIPStarRE.LDT.opTensor_mul,
                      _root_.LIDT.MIPStarRE.LDT.conjTranspose_opTensor]
              _ ≤ _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (O * Oᴴ) := _root_.LIDT.MIPStarRE.LDT.opTensor_le_leftTensor hOpos hRle
              _ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                    (_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_orderedHalf params family hi q gs *
                      (_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_orderedHalf params family hi q gs)ᴴ) := by
                    rfl
      _ = 1 := by
            calc
              ∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params (i + 1),
                  _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                    (_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_orderedHalf params family hi q gs *
                      (_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_orderedHalf params family hi q gs)ᴴ)
                  = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                      (∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params (i + 1),
                        _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_orderedHalf params family hi q gs *
                          (_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_orderedHalf params family hi q gs)ᴴ) := by
                    rw [← _root_.LIDT.MIPStarRE.LDT.leftTensor_finset_sum (ι₂ := ι) Finset.univ]
              _ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) := by
                    congr 1
                    have hsum :=
                      (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSandwichFamily params family (i + 1)
                        (fun j => q.2 ⟨j.1, by omega⟩)).sum_eq_total
                    simpa [_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSandwichFamily, _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_orderedHalf,
                      _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductTotalOperator_eq_one] using hsum
              _ = 1 := by simp [_root_.LIDT.MIPStarRE.LDT.leftTensor]
  · intro q
    classical
    calc
      ∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params (i + 1),
          (∑ u : Unit, _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_Csecond params strategy family hi q gs u) *
            (∑ u : Unit, _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_Csecond params strategy family hi q gs u)ᴴ
          ≤ ∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params (i + 1),
              _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                (_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_rotatedHalf params family hi q gs *
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_rotatedHalf params family hi q gs)ᴴ) := by
            refine Finset.sum_le_sum ?_
            intro gs _hgs
            let O : _root_.LIDT.MIPStarRE.Quantum.Op ι :=
              _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_rotatedHalf params family hi q gs
            let R : _root_.LIDT.MIPStarRE.Quantum.Op ι :=
              _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_rightComplement params strategy family q gs
            have hRle : R * Rᴴ ≤ 1 := by
              dsimp [R, _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_rightComplement]
              split
              · simp
              · rename_i a _ha
                let B : _root_.LIDT.MIPStarRE.Quantum.Op ι :=
                  ((_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointRightFamily params strategy family k i) q).outcome
                    (some a)
                have hBpos : 0 ≤ B := by
                  simpa [B] using
                    ((_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointRightFamily params strategy family k i) q).outcome_pos
                      (some a)
                have hBle : B ≤ 1 := by
                  simpa [B] using
                    _root_.LIDT.MIPStarRE.LDT.SubMeas.outcome_le_one
                      ((_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointRightFamily params strategy family k i) q)
                      (some a)
                have hRpos : 0 ≤ (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) - B := sub_nonneg.mpr hBle
                have hRle_one : (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) - B ≤ 1 := by
                  simpa [sub_eq_add_neg] using sub_le_self (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) hBpos
                have hRherm : ((1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) - B)ᴴ = 1 - B := by
                  simp [B, _root_.LIDT.MIPStarRE.LDT.SubMeas.outcome_hermitian]
                calc
                  ((1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) - B) * ((1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) - B)ᴴ
                      = (1 - B) * (1 - B) := by rw [hRherm]
                  _ ≤ 1 - B := _root_.LIDT.MIPStarRE.Quantum.sq_le_self hRpos hRle_one
                  _ ≤ 1 := hRle_one
            have hOpos : 0 ≤ O * Oᴴ := by
              simpa [O] using (Matrix.posSemidef_self_mul_conjTranspose O).nonneg
            calc
              (∑ u : Unit, _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_Csecond params strategy family hi q gs u) *
                  (∑ u : Unit,
                    _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_Csecond params strategy family hi q gs u)ᴴ
                  = _root_.LIDT.MIPStarRE.LDT.opTensor (O * Oᴴ) (R * Rᴴ) := by
                    simp [O, R, _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_Csecond, _root_.LIDT.MIPStarRE.LDT.opTensor_mul,
                      _root_.LIDT.MIPStarRE.LDT.conjTranspose_opTensor]
              _ ≤ _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (O * Oᴴ) := _root_.LIDT.MIPStarRE.LDT.opTensor_le_leftTensor hOpos hRle
              _ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                    (_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_rotatedHalf params family hi q gs *
                      (_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_rotatedHalf params family hi q gs)ᴴ) := by
                    rfl
      _ = 1 := by
            calc
              ∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params (i + 1),
                  _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                    (_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_rotatedHalf params family hi q gs *
                      (_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_rotatedHalf params family hi q gs)ᴴ)
                  = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                      (∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params (i + 1),
                        _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_rotatedHalf params family hi q gs *
                          (_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_rotatedHalf params family hi q gs)ᴴ) := by
                    rw [← _root_.LIDT.MIPStarRE.LDT.leftTensor_finset_sum (ι₂ := ι) Finset.univ]
              _ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) := by
                    congr 1
                    let xs : _root_.LIDT.MIPStarRE.LDT.PointTuple params (i + 1) :=
                      (_root_.LIDT.MIPStarRE.LDT.Pasting.pointTupleLastFrontEquiv params i) (fun j => q.2 ⟨j.1, by omega⟩)
                    have hperm :
                        (∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params (i + 1),
                          _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_rotatedHalf params family hi q gs *
                            (_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_rotatedHalf params family hi q gs)ᴴ) =
                        ∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params (i + 1),
                          _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family (i + 1) xs gs *
                            (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family (i + 1) xs gs)ᴴ := by
                      exact Fintype.sum_equiv (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleOutcomeLastFrontEquiv params i)
                        (fun gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params (i + 1) =>
                          _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_rotatedHalf params family hi q gs *
                            (_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_rotatedHalf params family hi q gs)ᴴ)
                        (fun gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params (i + 1) =>
                          _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family (i + 1) xs gs *
                            (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family (i + 1) xs gs)ᴴ)
                        (by
                          intro gs
                          simp [xs, _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_rotatedHalf])
                    have hsum := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSandwichFamily params family (i + 1) xs).sum_eq_total
                    rw [hperm]
                    simpa [_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSandwichFamily, _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductTotalOperator_eq_one] using hsum
              _ = 1 := by simp [_root_.LIDT.MIPStarRE.LDT.leftTensor]
  · unfold _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePoint_prefix_sourceOutcomeSum
      _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_firstSourceRaw
    apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
    intro q
    classical
    let evalOutcome : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params (i + 1) → Option (_root_.LIDT.MIPStarRE.LDT.Fq params) := fun gs =>
      Option.map (fun g : _root_.LIDT.MIPStarRE.LDT.Polynomial params => g q.1)
        (gs ⟨i, Nat.lt_succ_self i⟩)
    let O : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params (i + 1) → _root_.LIDT.MIPStarRE.Quantum.Op ι := fun gs =>
      _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_orderedHalf params family hi q gs
    let R : _root_.LIDT.MIPStarRE.LDT.Fq params → _root_.LIDT.MIPStarRE.Quantum.Op ι := fun a =>
      1 - ((_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointRightFamily params strategy family k i) q).outcome (some a)
    calc
      ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params,
          _root_.LIDT.MIPStarRE.LDT.ev strategy.state
            (_root_.LIDT.MIPStarRE.LDT.opTensor
              ((_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointPrefixOriginalFamily params family hi q).outcome (some a))
              (1 -
                (_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointRightFamily params strategy family k i q).outcome (some a)))
          = ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params,
              _root_.LIDT.MIPStarRE.LDT.ev strategy.state
                (_root_.LIDT.MIPStarRE.LDT.opTensor
                  (∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params (i + 1),
                    if evalOutcome gs = some a then O gs * (O gs)ᴴ else 0)
                  (R a)) := by
                simp [evalOutcome, O, R,
                  _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointPrefixOriginalFamily_outcome_some params family hi q,
                  _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_orderedHalf]
      _ = ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params, ∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params (i + 1),
              _root_.LIDT.MIPStarRE.LDT.ev strategy.state
                (_root_.LIDT.MIPStarRE.LDT.opTensor (if evalOutcome gs = some a then O gs * (O gs)ᴴ else 0) (R a)) := by
            refine Finset.sum_congr rfl ?_
            intro a _ha
            rw [_root_.LIDT.MIPStarRE.LDT.opTensor_sum_left_univ, _root_.LIDT.MIPStarRE.LDT.ev_sum]
      _ = ∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params (i + 1), ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params,
              _root_.LIDT.MIPStarRE.LDT.ev strategy.state
                (_root_.LIDT.MIPStarRE.LDT.opTensor (if evalOutcome gs = some a then O gs * (O gs)ᴴ else 0) (R a)) := by
            rw [Finset.sum_comm]
      _ = ∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params (i + 1),
              _root_.LIDT.MIPStarRE.LDT.ev strategy.state
                (_root_.LIDT.MIPStarRE.LDT.opTensor (O gs * (O gs)ᴴ)
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_rightComplement params strategy family q gs)) := by
            refine Finset.sum_congr rfl ?_
            intro gs _hgs
            cases hgs : evalOutcome gs with
            | none =>
                simp [evalOutcome, R, _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_rightComplement, hgs,
                  _root_.LIDT.MIPStarRE.LDT.opTensor, _root_.LIDT.MIPStarRE.LDT.ev_zero]
            | some a0 =>
                rw [Finset.sum_eq_single a0]
                · simp [evalOutcome, R, _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_rightComplement, hgs]
                · intro b _hb hb_ne
                  simp [Ne.symm hb_ne, _root_.LIDT.MIPStarRE.LDT.opTensor, _root_.LIDT.MIPStarRE.LDT.ev_zero]
                · intro hnot
                  simp at hnot
      _ = ∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params (i + 1), ∑ u : Unit,
              _root_.LIDT.MIPStarRE.LDT.ev strategy.state
                (_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_Aord params family hi q gs *
                  _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_Cfirst params strategy family hi q gs u) := by
            refine Finset.sum_congr rfl ?_
            intro gs _hgs
            rw [Fintype.sum_unique]
            change _root_.LIDT.MIPStarRE.LDT.ev strategy.state
                (_root_.LIDT.MIPStarRE.LDT.opTensor (O gs * (O gs)ᴴ)
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_rightComplement params strategy family q gs)) =
              _root_.LIDT.MIPStarRE.LDT.ev strategy.state
                (_root_.LIDT.MIPStarRE.LDT.opTensor (O gs) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) *
                  _root_.LIDT.MIPStarRE.LDT.opTensor ((O gs)ᴴ)
                    (_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_rightComplement params strategy family q gs))
            rw [_root_.LIDT.MIPStarRE.LDT.opTensor_mul]
            simp
  · unfold _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePoint_prefix_afterFirstCSOutcomeSum
      _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_firstTargetRaw
    apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
    intro q
    classical
    let evalOutcome : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params (i + 1) → Option (_root_.LIDT.MIPStarRE.LDT.Fq params) := fun gs =>
      Option.map (fun g : _root_.LIDT.MIPStarRE.LDT.Polynomial params => g q.1)
        (gs ⟨i, Nat.lt_succ_self i⟩)
    refine Finset.sum_congr rfl ?_
    intro gs _hgs
    cases hgs : evalOutcome gs with
    | none =>
        simp [evalOutcome, _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_Arot,
          _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_Cfirst, _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_orderedHalf,
          _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_rotatedHalf,
          _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_rightComplement, hgs, _root_.LIDT.MIPStarRE.LDT.opTensor, _root_.LIDT.MIPStarRE.LDT.ev_zero]
    | some a =>
        rw [Fintype.sum_unique]
        simp [evalOutcome, hgs, _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_Arot,
          _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_Cfirst, _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_orderedHalf,
          _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_rotatedHalf,
          _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_rightComplement, _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_opTensor]
  · unfold _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePoint_prefix_afterFirstCSOutcomeSum
      _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_secondSourceRaw
    apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
    intro q
    classical
    let evalOutcome : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params (i + 1) → Option (_root_.LIDT.MIPStarRE.LDT.Fq params) := fun gs =>
      Option.map (fun g : _root_.LIDT.MIPStarRE.LDT.Polynomial params => g q.1)
        (gs ⟨i, Nat.lt_succ_self i⟩)
    refine Finset.sum_congr rfl ?_
    intro gs _hgs
    cases hgs : evalOutcome gs with
    | none =>
        simp [evalOutcome, _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_Aord,
          _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_Csecond,
          _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_rightComplement, hgs, _root_.LIDT.MIPStarRE.LDT.opTensor, _root_.LIDT.MIPStarRE.LDT.ev_zero]
    | some a =>
        rw [Fintype.sum_unique]
        simp [evalOutcome, hgs, _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_Aord,
          _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_Csecond, _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_orderedHalf,
          _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_rotatedHalf,
          _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_rightComplement, _root_.LIDT.MIPStarRE.LDT.opTensor_mul_leftTensor]
  · unfold _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePoint_prefix_movedOutcomeSum
      _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_secondTargetRaw
    apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
    intro q
    classical
    let e : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params (i + 1) ≃ _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params (i + 1) :=
      _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleOutcomeLastFrontEquiv params i
    let xsMoved : _root_.LIDT.MIPStarRE.LDT.PointTuple params (i + 1) :=
      Fin.cons (q.2 ⟨i, hi⟩) (fun j => q.2 ⟨j.1, by omega⟩)
    let movedEval : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params (i + 1) → Option (_root_.LIDT.MIPStarRE.LDT.Fq params) := fun gs =>
      Option.map (fun g : _root_.LIDT.MIPStarRE.LDT.Polynomial params => g q.1) (gs 0)
    let movedHalf : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params (i + 1) → _root_.LIDT.MIPStarRE.Quantum.Op ι := fun gs =>
      _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family (i + 1) xsMoved gs
    let R : _root_.LIDT.MIPStarRE.LDT.Fq params → _root_.LIDT.MIPStarRE.Quantum.Op ι := fun a =>
      1 - ((_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointRightFamily params strategy family k i) q).outcome (some a)
    calc
      ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params,
          _root_.LIDT.MIPStarRE.LDT.ev strategy.state
            (_root_.LIDT.MIPStarRE.LDT.opTensor
              ((_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointPrefixMovedFamily params family hi q).outcome (some a))
              (1 -
                (_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointRightFamily params strategy family k i q).outcome (some a)))
          = ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params,
              _root_.LIDT.MIPStarRE.LDT.ev strategy.state
                (_root_.LIDT.MIPStarRE.LDT.opTensor
                  (∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params (i + 1),
                    if movedEval gs = some a then movedHalf gs * (movedHalf gs)ᴴ else 0)
                  (R a)) := by
                simp [movedEval, movedHalf, xsMoved, R,
                  _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointPrefixMovedFamily_outcome_some params family hi q]
      _ = ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params, ∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params (i + 1),
              _root_.LIDT.MIPStarRE.LDT.ev strategy.state
                (_root_.LIDT.MIPStarRE.LDT.opTensor (if movedEval gs = some a then movedHalf gs * (movedHalf gs)ᴴ else 0)
                  (R a)) := by
            refine Finset.sum_congr rfl ?_
            intro a _ha
            rw [_root_.LIDT.MIPStarRE.LDT.opTensor_sum_left_univ, _root_.LIDT.MIPStarRE.LDT.ev_sum]
      _ = ∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params (i + 1), ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params,
              _root_.LIDT.MIPStarRE.LDT.ev strategy.state
                (_root_.LIDT.MIPStarRE.LDT.opTensor (if movedEval gs = some a then movedHalf gs * (movedHalf gs)ᴴ else 0)
                  (R a)) := by
            rw [Finset.sum_comm]
      _ = ∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params (i + 1),
              _root_.LIDT.MIPStarRE.LDT.ev strategy.state
                (_root_.LIDT.MIPStarRE.LDT.opTensor (movedHalf gs * (movedHalf gs)ᴴ)
                  (match movedEval gs with
                   | none => 0
                   | some a => R a)) := by
            refine Finset.sum_congr rfl ?_
            intro gs _hgs
            cases hgs : movedEval gs with
            | none =>
                simp [R, _root_.LIDT.MIPStarRE.LDT.opTensor, _root_.LIDT.MIPStarRE.LDT.ev_zero]
            | some a0 =>
                rw [Finset.sum_eq_single a0]
                · simp [R]
                · intro b _hb hb_ne
                  simp [Ne.symm hb_ne, _root_.LIDT.MIPStarRE.LDT.opTensor, _root_.LIDT.MIPStarRE.LDT.ev_zero]
                · intro hnot
                  simp at hnot
      _ = ∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params (i + 1),
              _root_.LIDT.MIPStarRE.LDT.ev strategy.state
                (_root_.LIDT.MIPStarRE.LDT.opTensor
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_rotatedHalf params family hi q gs *
                    (_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_rotatedHalf params family hi q gs)ᴴ)
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_rightComplement params strategy family q gs)) := by
            symm
            exact Fintype.sum_equiv e
              (fun gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params (i + 1) =>
                _root_.LIDT.MIPStarRE.LDT.ev strategy.state
                  (_root_.LIDT.MIPStarRE.LDT.opTensor
                    (_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_rotatedHalf params family hi q gs *
                      (_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_rotatedHalf params family hi q gs)ᴴ)
                    (_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_rightComplement params strategy family q gs)))
              (fun gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params (i + 1) =>
                _root_.LIDT.MIPStarRE.LDT.ev strategy.state
                  (_root_.LIDT.MIPStarRE.LDT.opTensor (movedHalf gs * (movedHalf gs)ᴴ)
                    (match movedEval gs with
                     | none => 0
                     | some a => R a)))
              (by
                intro gs
                unfold e movedHalf movedEval xsMoved R
                  _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_rotatedHalf
                  _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_rightComplement
                  _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleOutcomeLastFrontEquiv _root_.LIDT.MIPStarRE.LDT.Pasting.pointTupleLastFrontEquiv
                rfl)
      _ = ∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params (i + 1), ∑ u : Unit,
              _root_.LIDT.MIPStarRE.LDT.ev strategy.state
                (_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_Csecond params strategy family hi q gs u *
                  (_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_Arot params family hi q gs)ᴴ) := by
            refine Finset.sum_congr rfl ?_
            intro gs _hgs
            rw [Fintype.sum_unique]
            simp [_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_Arot, _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_Csecond,
              _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_rotatedHalf,
              _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_rightComplement, _root_.LIDT.MIPStarRE.LDT.opTensor_mul_leftTensor]
