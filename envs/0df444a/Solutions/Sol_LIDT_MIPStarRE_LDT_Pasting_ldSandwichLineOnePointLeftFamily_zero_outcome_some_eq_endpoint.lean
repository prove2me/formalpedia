-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointLeftFamily_zero_outcome_some_eq_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T16:17:05.561983+00:00
-- url     : https://prove2.me/submissions/bb7809a0-c9d3-4e37-87f7-099fbe55e276

-- Generated proof for MIPStarRE.LDT.Pasting.ldSandwichLineOnePointLeftFamily_zero_outcome_some_eq_endpoint.
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

/- Source helpers from MIPStarRE/LDT/Pasting/ComparisonLemmas/LdSandwichLineOnePoint/Endpoint.lean. -/
/-!
# Section 12 pasting: line one-point transport — endpoint lemmas

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







-- The proof lifts the endpoint consistency relation through the split
-- sandwiched-line equivalence; the chain of rewriting identities unfolds this
-- equivalence and the endpoint-family definition.


lemma gHatIdxMeas_outcome_some_eq_evaluateAt
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (x : Fq params) (u : Point params) (a : Fq params) :
    (∑ g : GHatOutcome params,
      if Option.map (fun g' : Polynomial params => g' u) g = some a then
        (gHatIdxMeas params family x).outcome g
      else
        0) =
      (evaluateAt params u ((family.meas x).toSubMeas)).outcome a := by
  rw [Fintype.sum_option]
  conv_lhs =>
    simp [gHatIdxMeas, completeSubMeas]
  conv_rhs =>
    simp [evaluateAt, postprocess, Finset.sum_filter]

lemma gHatSandwichFamily_restrict_zero_outcome_some
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {n : ℕ} (xs : PointTuple params (n + 1))
    (u : Point params) (a : Fq params) :
    (postprocess
      (restrictSubMeas (gHatSandwichFamily params family (n + 1) xs)
        (fun gs => (gs 0).isSome = true))
      (fun gs => Option.map (fun g : Polynomial params => g u) (gs 0))).outcome (some a) =
      ∑ gs : GHatTupleOutcome params (n + 1),
        if Option.map (fun g : Polynomial params => g u) (gs 0) = some a then
          let half := gHatHalfProductOutcomeOperator params family (n + 1) xs gs
          half * halfᴴ
        else
          0 := by
  conv_lhs =>
    simp [postprocess, restrictSubMeas, gHatSandwichFamily, Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro gs _hgs
  by_cases hmap : Option.map (fun g : Polynomial params => g u) (gs 0) = some a
  · rcases Option.map_eq_some_iff.mp hmap with ⟨g, hgs0, hg⟩
    simp [hgs0]
  · have hnone : ¬ ∃ g : Polynomial params, gs 0 = some g ∧ g u = a := by
      rintro ⟨g, hgs0, hg⟩
      exact hmap (Option.map_eq_some_iff.mpr ⟨g, hgs0, hg⟩)
    simp [hnone]














end MIPStarRE.LDT.Pasting

end

end LIDT

open LIDT
/-!
# Section 12 pasting: line one-point transport — endpoint lemmas

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







-- The proof lifts the endpoint consistency relation through the split
-- sandwiched-line equivalence; the chain of rewriting identities unfolds this
-- equivalence and the endpoint-family definition.

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters)
    [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (strategy : _root_.LIDT.MIPStarRE.LDT.SymStrat params.next ι)
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    {k : ℕ} (hk : 0 < k)
    (q : _root_.LIDT.MIPStarRE.LDT.Pasting.SandwichedLineQuestion params k) (a : _root_.LIDT.MIPStarRE.LDT.Fq params) :
    ((_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointLeftFamily params strategy family k 0) q).outcome (some a) =
      (_root_.LIDT.MIPStarRE.LDT.evaluateAt params q.1 ((family.meas (q.2 ⟨0, hk⟩)).toSubMeas)).outcome a := by
  cases k with
  | zero => cases hk
  | succ r =>
      let xs : _root_.LIDT.MIPStarRE.LDT.PointTuple params (r + 1) := q.2
      let u : _root_.LIDT.MIPStarRE.LDT.Point params := q.1
      let G : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params → _root_.LIDT.MIPStarRE.Quantum.Op ι := fun g =>
        (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family (xs 0)).outcome g
      let T : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params r → _root_.LIDT.MIPStarRE.Quantum.Op ι := fun gs =>
        _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family r (_root_.LIDT.MIPStarRE.LDT.Pasting.pointTupleTail xs) gs
      have hleft :
          ((_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointLeftFamily params strategy family (r + 1) 0) q).outcome
              (some a) =
            ∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params (r + 1),
              if Option.map (fun g : _root_.LIDT.MIPStarRE.LDT.Polynomial params => g u) (gs 0) = some a then
                let half := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family (r + 1) xs gs
                half * halfᴴ
              else
                0 := by
        simpa [_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointLeftFamily, xs, u] using
          _root_.LIDT.MIPStarRE.LDT.Pasting.gHatSandwichFamily_restrict_zero_outcome_some params family xs u a
      have hsplit :
          (∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params (r + 1),
            if Option.map (fun g : _root_.LIDT.MIPStarRE.LDT.Polynomial params => g u) (gs 0) = some a then
              let half := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family (r + 1) xs gs
              half * halfᴴ
            else
              0) =
            ∑ p : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params r,
              if Option.map (fun g : _root_.LIDT.MIPStarRE.LDT.Polynomial params => g u) p.1 = some a then
                (G p.1 * T p.2) * (G p.1 * T p.2)ᴴ
              else
                0 := by
        exact Fintype.sum_equiv (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleOutcomeConsEquiv' params r)
          (fun gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params (r + 1) =>
            if Option.map (fun g : _root_.LIDT.MIPStarRE.LDT.Polynomial params => g u) (gs 0) = some a then
              let half := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family (r + 1) xs gs
              half * halfᴴ
            else
              0)
          (fun p : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params r =>
            if Option.map (fun g : _root_.LIDT.MIPStarRE.LDT.Polynomial params => g u) p.1 = some a then
              (G p.1 * T p.2) * (G p.1 * T p.2)ᴴ
            else
              0)
          (by
            intro gs
            simp [_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleOutcomeConsEquiv', _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator, T, G])
      calc
        ((_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointLeftFamily params strategy family (r + 1) 0) q).outcome
            (some a)
            = ∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params (r + 1),
              if Option.map (fun g : _root_.LIDT.MIPStarRE.LDT.Polynomial params => g u) (gs 0) = some a then
                let half := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator params family (r + 1) xs gs
                half * halfᴴ
              else
                0 := hleft
        _ = ∑ p : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params r,
              if Option.map (fun g : _root_.LIDT.MIPStarRE.LDT.Polynomial params => g u) p.1 = some a then
                (G p.1 * T p.2) * (G p.1 * T p.2)ᴴ
              else
                0 := hsplit
        _ = ∑ g : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params,
              ∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params r,
                if Option.map (fun g' : _root_.LIDT.MIPStarRE.LDT.Polynomial params => g' u) g = some a then
                  (G g * T gs) * (G g * T gs)ᴴ
                else
                  0 := by
              rw [← Finset.univ_product_univ, Finset.sum_product]
        _ = ∑ g : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params,
              if Option.map (fun g' : _root_.LIDT.MIPStarRE.LDT.Polynomial params => g' u) g = some a then
                G g
              else
                0 := by
              refine Finset.sum_congr rfl ?_
              intro g _hg
              by_cases hmap : Option.map (fun g' : _root_.LIDT.MIPStarRE.LDT.Polynomial params => g' u) g = some a
              · have hherm : (G g)ᴴ = G g := by
                  simpa [G] using (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family (xs 0)).outcome_hermitian g
                have hproj : G g * G g = G g := by
                  simpa [G] using _root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas_proj params family (xs 0) g
                calc
                  (∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params r,
                    if Option.map (fun g' : _root_.LIDT.MIPStarRE.LDT.Polynomial params => g' u) g = some a then
                      (G g * T gs) * (G g * T gs)ᴴ
                    else
                      0) = ∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params r,
                        G g * (T gs * (T gs)ᴴ) * G g := by
                        refine Finset.sum_congr rfl ?_
                        intro gs _hgs
                        simp [hmap, Matrix.conjTranspose_mul, hherm, mul_assoc]
                  _ = G g *
                        (∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params r, T gs * (T gs)ᴴ) * G g := by
                        rw [← Finset.sum_mul, ← Matrix.mul_sum]
                  _ = G g := by
                        have htail :
                            (∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params r, T gs * (T gs)ᴴ) = 1 := by
                          simpa [T, _root_.LIDT.MIPStarRE.LDT.Pasting.gHatSandwichFamily,
                            _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfProductTotalOperator_eq_one] using
                            (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSandwichFamily params family r (_root_.LIDT.MIPStarRE.LDT.Pasting.pointTupleTail xs)).sum_eq_total
                        simp [htail, hproj]
                  _ = if Option.map (fun g' : _root_.LIDT.MIPStarRE.LDT.Polynomial params => g' u) g = some a then
                        G g
                      else
                        0 := by
                        simp [hmap]
              · simp [hmap]
        _ = (_root_.LIDT.MIPStarRE.LDT.evaluateAt params u ((family.meas (xs 0)).toSubMeas)).outcome a := by
              simpa [G] using
                _root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas_outcome_some_eq_evaluateAt params family (xs 0) u a
