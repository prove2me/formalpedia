-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointLeftFamily_drop_last_outcome_some
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T16:29:11.766986+00:00
-- url     : https://prove2.me/submissions/933146a4-d1d1-4ec2-8b46-5a311c0614fb

-- Generated proof for MIPStarRE.LDT.Pasting.ldSandwichLineOnePointLeftFamily_drop_last_outcome_some.
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_gHatSandwich_sum_last_eq_prefix

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









/-- Outcome expansion for the original full one-point left family at a concrete field value. -/
lemma ldSandwichLineOnePointLeftFamily_outcome_some
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k)
    (q : SandwichedLineQuestion params k)
    (a : Fq params) :
    ((ldSandwichLineOnePointLeftFamily params strategy family k i) q).outcome (some a) =
      ∑ gs : GHatTupleOutcome params k,
        if Option.map (fun g : Polynomial params => g q.1) (gs ⟨i, hi⟩) = some a then
          let half := gHatHalfProductOutcomeOperator params family k q.2 gs
          half * halfᴴ
        else
          0 := by
  simpa [ldSandwichLineOnePointLeftFamily, hi] using
    gHatSandwichFamily_restrict_eval_outcome_some
      params family q.2 ⟨i, hi⟩ q.1 a













-- This arithmetic absorption proof expands several nested error estimates from the paper.



end MIPStarRE.LDT.Pasting

end

end LIDT

open LIDT
/-!
# Section 12 pasting: line one-point transport — outcome lemmas

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
    {n i : ℕ} (hi : i < n)
    (q : _root_.LIDT.MIPStarRE.LDT.Pasting.SandwichedLineQuestion params (n + 1))
    (a : _root_.LIDT.MIPStarRE.LDT.Fq params) :
    ((_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointLeftFamily params strategy family (n + 1) i) q).outcome
        (some a) =
      ((_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointLeftFamily params strategy family n i)
        (q.1, fun j => q.2 ⟨j.1, by omega⟩)).outcome (some a) := by
  let qPrefix : _root_.LIDT.MIPStarRE.LDT.Pasting.SandwichedLineQuestion params n := (q.1, fun j => q.2 ⟨j.1, by omega⟩)
  have hiFull : i < n + 1 := by omega
  rw [_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointLeftFamily_outcome_some params strategy family hiFull q a]
  rw [_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointLeftFamily_outcome_some params strategy family hi qPrefix a]
  let e := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleOutcomePrefixLastEquiv params n
  have hsplit :
      (∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params (n + 1),
        if Option.map (fun g : _root_.LIDT.MIPStarRE.LDT.Polynomial params => g q.1) (gs ⟨i, hiFull⟩) = some a then
          let half := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family (n + 1) q.2 gs
          half * halfᴴ
        else
          0) =
      ∑ p : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params,
        if Option.map (fun g : _root_.LIDT.MIPStarRE.LDT.Polynomial params => g q.1) (p.1 ⟨i, hi⟩) = some a then
          let half := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family (n + 1) q.2 (e.symm p)
          half * halfᴴ
        else
          0 := by
    exact Fintype.sum_equiv e
      (fun gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params (n + 1) =>
        if Option.map (fun g : _root_.LIDT.MIPStarRE.LDT.Polynomial params => g q.1) (gs ⟨i, hiFull⟩) = some a then
          let half := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family (n + 1) q.2 gs
          half * halfᴴ
        else
          0)
      (fun p : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params =>
        if Option.map (fun g : _root_.LIDT.MIPStarRE.LDT.Polynomial params => g q.1) (p.1 ⟨i, hi⟩) = some a then
          let half := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family (n + 1) q.2 (e.symm p)
          half * halfᴴ
        else
          0)
      (by
        intro gs
        have hleft : e.symm (e gs) = gs := by
          exact e.left_inv gs
        rw [hleft]
        simp [e, _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleOutcomePrefixLastEquiv])
  calc
    (∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params (n + 1),
        if Option.map (fun g : _root_.LIDT.MIPStarRE.LDT.Polynomial params => g q.1) (gs ⟨i, hiFull⟩) = some a then
          let half := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family (n + 1) q.2 gs
          half * halfᴴ
        else
          0)
        = ∑ p : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params,
            if Option.map (fun g : _root_.LIDT.MIPStarRE.LDT.Polynomial params => g q.1) (p.1 ⟨i, hi⟩) = some a then
              let half := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family (n + 1) q.2 (e.symm p)
              half * halfᴴ
            else
              0 := hsplit
    _ = ∑ gsPrefix : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n,
          ∑ g : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params,
            if Option.map (fun g' : _root_.LIDT.MIPStarRE.LDT.Polynomial params => g' q.1) (gsPrefix ⟨i, hi⟩) = some a then
              let half := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family (n + 1) q.2
                (e.symm (gsPrefix, g))
              half * halfᴴ
            else
              0 := by
          rw [← Finset.univ_product_univ, Finset.sum_product]
    _ = ∑ gsPrefix : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params n,
          if Option.map (fun g : _root_.LIDT.MIPStarRE.LDT.Polynomial params => g q.1) (gsPrefix ⟨i, hi⟩) = some a then
            let half := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n qPrefix.2 gsPrefix
            half * halfᴴ
          else
            0 := by
          refine Finset.sum_congr rfl ?_
          intro gsPrefix _hgs
          by_cases hmatch : Option.map (fun g : _root_.LIDT.MIPStarRE.LDT.Polynomial params => g q.1)
              (gsPrefix ⟨i, hi⟩) = some a
          · calc
              (∑ g : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params,
                if Option.map (fun g' : _root_.LIDT.MIPStarRE.LDT.Polynomial params => g' q.1)
                    (gsPrefix ⟨i, hi⟩) = some a then
                  let half := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family (n + 1) q.2
                    (e.symm (gsPrefix, g))
                  half * halfᴴ
                else
                  0)
                  = ∑ g : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params,
                      let half := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family (n + 1) q.2
                        (e.symm (gsPrefix, g))
                      half * halfᴴ := by
                    simp [hmatch]
              _ = _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n qPrefix.2 gsPrefix *
                    (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n qPrefix.2 gsPrefix)ᴴ := by
                    simpa [qPrefix, e] using
                      _root_.LIDT.MIPStarRE.LDT.Pasting.gHatSandwich_sum_last_eq_prefix params family n q.2 gsPrefix
              _ = if Option.map (fun g : _root_.LIDT.MIPStarRE.LDT.Polynomial params => g q.1)
                    (gsPrefix ⟨i, hi⟩) = some a then
                    let half := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family n qPrefix.2 gsPrefix
                    half * halfᴴ
                  else
                    0 := by
                    simp [hmatch]
          · simp [hmatch]
