-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePoint_prefix_linearDefect_average_cauchySchwarz_bound
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T16:44:31.555284+00:00
-- url     : https://prove2.me/submissions/01576cfa-9f29-46a2-9bc7-7021abb3cfc4

-- Generated proof for MIPStarRE.LDT.Pasting.ldSandwichLineOnePoint_prefix_linearDefect_average_cauchySchwarz_bound.
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_ldSandwichLineOnePoint_prefix_outcomeSum_cauchySchwarz_bound
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_qBipartiteLinearConsDefect_option_eq_sum_some_complement

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

/-- The postprocessed one-point right family has zero-operator `none` outcome,
because the selected slot satisfies `i < k` and is always postprocessed to `some`. -/
lemma ldSandwichLineOnePointRightFamily_outcome_none_eq_zero
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k)
    (q : SandwichedLineQuestion params k) :
    ((ldSandwichLineOnePointRightFamily params strategy family k i) q).outcome none = 0 := by
  simp [ldSandwichLineOnePointRightFamily, postprocess, hi]

/-- The one-point right family is measurement-valued when the selected coordinate
exists.  This is the source of nonnegativity for the linear consistency defect. -/
lemma ldSandwichLineOnePointRightFamily_total_eq_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k)
    (q : SandwichedLineQuestion params k) :
    ((ldSandwichLineOnePointRightFamily params strategy family k i) q).total = 1 := by
  let ℓ : AxisParallelLine params.next :=
    { base := appendPoint params q.1 zeroCoord
      direction := lastCoord params }
  simpa [ldSandwichLineOnePointRightFamily, verticalLineMeasurementFamily, hi,
    postprocess_total, ℓ] using (strategy.axisParallelMeasurement ℓ).total_eq_one

/-- The rotated prefix-only one-point left family has no `none` outcome. -/
lemma ldSandwichLineOnePointPrefixMovedFamily_outcome_none_eq_zero
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k)
    (q : SandwichedLineQuestion params k) :
    (ldSandwichLineOnePointPrefixMovedFamily params family hi q).outcome none = 0 := by
  conv_lhs =>
    simp [ldSandwichLineOnePointPrefixMovedFamily, postprocess, restrictSubMeas,
      Finset.sum_filter]
  apply Finset.sum_eq_zero
  intro gs _hgs
  by_cases hsome : (gs 0).isSome = true
  · rcases Option.isSome_iff_exists.mp hsome with ⟨g, hg⟩
    simp [hg]
  · simp [hsome]











/-- The prefix-only one-point left family has no `none` outcome. -/
lemma ldSandwichLineOnePointPrefixOriginalFamily_outcome_none_eq_zero
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k)
    (q : SandwichedLineQuestion params k) :
    (ldSandwichLineOnePointPrefixOriginalFamily params family hi q).outcome none = 0 := by
  conv_lhs =>
    simp [ldSandwichLineOnePointPrefixOriginalFamily, postprocess, restrictSubMeas,
      Finset.sum_filter]
  apply Finset.sum_eq_zero
  intro gs _hgs
  by_cases hsome : (gs ⟨i, Nat.lt_succ_self i⟩).isSome = true
  · rcases Option.isSome_iff_exists.mp hsome with ⟨g, hg⟩
    simp [hg]
  · simp [hsome]





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
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SandwichedLineQuestion params k)) (fun q =>
      _root_.LIDT.MIPStarRE.LDT.Pasting.qBipartiteLinearConsDefect strategy.state
        ((_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointPrefixOriginalFamily params family hi) q)
        ((_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointRightFamily params strategy family k i) q))
      ≤
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SandwichedLineQuestion params k)) (fun q =>
      _root_.LIDT.MIPStarRE.LDT.Pasting.qBipartiteLinearConsDefect strategy.state
        ((_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointPrefixMovedFamily params family hi) q)
        ((_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointRightFamily params strategy family k i) q)) +
      2 * Real.sqrt (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwichError params gamma zeta (i + 1)) := by
  let 𝒟 : _root_.LIDT.MIPStarRE.LDT.Distribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SandwichedLineQuestion params k) :=
    _root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SandwichedLineQuestion params k)
  let A₀ : _root_.LIDT.MIPStarRE.LDT.IdxSubMeas (_root_.LIDT.MIPStarRE.LDT.Pasting.SandwichedLineQuestion params k) (Option (_root_.LIDT.MIPStarRE.LDT.Fq params)) ι :=
    _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointPrefixOriginalFamily params family hi
  let A₁ : _root_.LIDT.MIPStarRE.LDT.IdxSubMeas (_root_.LIDT.MIPStarRE.LDT.Pasting.SandwichedLineQuestion params k) (Option (_root_.LIDT.MIPStarRE.LDT.Fq params)) ι :=
    _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointPrefixMovedFamily params family hi
  let C : _root_.LIDT.MIPStarRE.LDT.IdxSubMeas (_root_.LIDT.MIPStarRE.LDT.Pasting.SandwichedLineQuestion params k) (Option (_root_.LIDT.MIPStarRE.LDT.Fq params)) ι :=
    _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointRightFamily params strategy family k i
  have hsource :
      _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => _root_.LIDT.MIPStarRE.LDT.Pasting.qBipartiteLinearConsDefect strategy.state (A₀ q) (C q)) =
        _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q =>
          ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params,
            _root_.LIDT.MIPStarRE.LDT.ev strategy.state (_root_.LIDT.MIPStarRE.LDT.opTensor ((A₀ q).outcome (some a))
              (1 - (C q).outcome (some a)))) := by
    apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
    intro q
    exact _root_.LIDT.MIPStarRE.LDT.Pasting.qBipartiteLinearConsDefect_option_eq_sum_some_complement
      strategy.state (A₀ q) (C q)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointRightFamily_total_eq_one params strategy family hi q)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointPrefixOriginalFamily_outcome_none_eq_zero params family hi q)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointRightFamily_outcome_none_eq_zero params strategy family hi q)
  have hmoved :
      _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => _root_.LIDT.MIPStarRE.LDT.Pasting.qBipartiteLinearConsDefect strategy.state (A₁ q) (C q)) =
        _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q =>
          ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params,
            _root_.LIDT.MIPStarRE.LDT.ev strategy.state (_root_.LIDT.MIPStarRE.LDT.opTensor ((A₁ q).outcome (some a))
              (1 - (C q).outcome (some a)))) := by
    apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
    intro q
    exact _root_.LIDT.MIPStarRE.LDT.Pasting.qBipartiteLinearConsDefect_option_eq_sum_some_complement
      strategy.state (A₁ q) (C q)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointRightFamily_total_eq_one params strategy family hi q)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointPrefixMovedFamily_outcome_none_eq_zero params family hi q)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointRightFamily_outcome_none_eq_zero params strategy family hi q)
  have hexpanded :=
    _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePoint_prefix_outcomeSum_cauchySchwarz_bound
      params strategy family gamma zeta hi hi0 facts
  simpa [𝒟, A₀, A₁, C] using
    (calc
      _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => _root_.LIDT.MIPStarRE.LDT.Pasting.qBipartiteLinearConsDefect strategy.state (A₀ q) (C q))
          = _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q =>
              ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params,
                _root_.LIDT.MIPStarRE.LDT.ev strategy.state (_root_.LIDT.MIPStarRE.LDT.opTensor ((A₀ q).outcome (some a))
                  (1 - (C q).outcome (some a)))) := hsource
      _ ≤ _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q =>
              ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params,
                _root_.LIDT.MIPStarRE.LDT.ev strategy.state (_root_.LIDT.MIPStarRE.LDT.opTensor ((A₁ q).outcome (some a))
                  (1 - (C q).outcome (some a)))) +
            2 * Real.sqrt (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwichError params gamma zeta (i + 1)) := by
              simpa [𝒟, A₀, A₁, C] using hexpanded
      _ = _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => _root_.LIDT.MIPStarRE.LDT.Pasting.qBipartiteLinearConsDefect strategy.state (A₁ q) (C q)) +
            2 * Real.sqrt (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwichError params gamma zeta (i + 1)) := by
              rw [← hmoved])
