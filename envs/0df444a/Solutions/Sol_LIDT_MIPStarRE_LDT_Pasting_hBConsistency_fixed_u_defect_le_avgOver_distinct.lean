-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.hBConsistency_fixed_u_defect_le_avgOver_distinct
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T16:36:31.84199+00:00
-- url     : https://prove2.me/submissions/80101df8-1107-45b0-a91c-e9557b26c245

-- Generated proof for MIPStarRE.LDT.Pasting.hBConsistency_fixed_u_defect_le_avgOver_distinct.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LineInterpolation_BadLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LineInterpolation_BadMass
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LineInterpolation_Core
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

/- Source helpers from MIPStarRE/LDT/Pasting/ComparisonLemmas/LineInterpolation/Averaging.lean. -/
/-!
# Line interpolation: averaging and tensor helpers

Tensor/average helper lemmas and total-variation comparison used across the
line interpolation error bounding chain.

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





lemma max_zero_add_le
    (a t : Error) (ha : 0 ≤ a) :
    max 0 (a + t) ≤ a + max 0 t := by
  by_cases ht : 0 ≤ t
  · rw [max_eq_right (add_nonneg ha ht), max_eq_right ht]
  · have ht' : t ≤ 0 := le_of_not_ge ht
    by_cases hat : 0 ≤ a + t
    · rw [max_eq_right hat, max_eq_left ht']
      linarith
    · have hat' : a + t ≤ 0 := le_of_not_ge hat
      rw [max_eq_left hat', max_eq_left ht']
      linarith

lemma max_zero_mul_add_le
    (w a t : Error)
    (hw : 0 ≤ w) :
    max 0 (w * a + t) ≤ w * max 0 a + max 0 t := by
  have hwa : w * a ≤ w * max 0 a := by
    exact mul_le_mul_of_nonneg_left (le_max_right 0 a) hw
  calc
    max 0 (w * a + t) ≤ max 0 (w * max 0 a + t) := by
      have hadd : w * a + t ≤ w * max 0 a + t := by linarith
      exact max_le_max le_rfl hadd
    _ ≤ w * max 0 a + max 0 t := by
      exact max_zero_add_le (w * max 0 a) t (mul_nonneg hw (by positivity))

lemma max_zero_avgOver_le_avgOver_max_zero
    {α : Type*}
    (𝒟 : Distribution α)
    (f : α → Error) :
    max 0 (avgOver 𝒟 f) ≤ avgOver 𝒟 (fun a => max 0 (f a)) := by
  classical
  unfold avgOver
  induction 𝒟.support using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      calc
        max 0 (𝒟.weight a * f a + ∑ x ∈ s, 𝒟.weight x * f x)
          ≤ 𝒟.weight a * max 0 (f a) + max 0 (∑ x ∈ s, 𝒟.weight x * f x) := by
              exact max_zero_mul_add_le (𝒟.weight a) (f a)
                (∑ x ∈ s, 𝒟.weight x * f x) (𝒟.nonnegative a)
        _ ≤ 𝒟.weight a * max 0 (f a) + ∑ x ∈ s, 𝒟.weight x * max 0 (f x) := by
              simpa [add_comm, add_left_comm, add_assoc] using
                add_le_add_right ih (𝒟.weight a * max 0 (f a))

lemma qBipartiteMatchMass_averageIdxSubMeas_left
    {Question Outcome : Type*}
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι)
    (B : SubMeas Outcome ι)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1) :
    qBipartiteMatchMass ψ (averageIdxSubMeas 𝒟 A h𝒟) B =
      avgOver 𝒟 (fun q => qBipartiteMatchMass ψ (A q) B) := by
  classical
  unfold qBipartiteMatchMass averageIdxSubMeas
  calc
    ∑ a,
        ev ψ
          (opTensor (averageOperatorOverDistribution 𝒟 (fun q => (A q).outcome a))
            (B.outcome a))
      = ∑ a, avgOver 𝒟
          (fun q => ev ψ (opTensor ((A q).outcome a) (B.outcome a))) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              exact ev_opTensor_averageOperatorOverDistribution_left ψ 𝒟
                (fun q => (A q).outcome a) (B.outcome a)
    _ = avgOver 𝒟
          (fun q => ∑ a, ev ψ (opTensor ((A q).outcome a) (B.outcome a))) := by
          rw [← avgOver_sum]
    _ = avgOver 𝒟 (fun q => qBipartiteMatchMass ψ (A q) B) := by
          simp [avgOver, qBipartiteMatchMass]

lemma ev_opTensor_total_averageIdxSubMeas_left
    {Question Outcome : Type*}
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι)
    (B : SubMeas Outcome ι)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1) :
    ev ψ (opTensor (averageIdxSubMeas 𝒟 A h𝒟).total B.total) =
      avgOver 𝒟 (fun q => ev ψ (opTensor (A q).total B.total)) := by
  classical
  unfold averageIdxSubMeas
  change ev ψ (opTensor (averageOperatorOverDistribution 𝒟 (fun q => (A q).total)) B.total) = _
  exact ev_opTensor_averageOperatorOverDistribution_left ψ 𝒟 (fun q => (A q).total) B.total

lemma qBipartiteConsDefect_averageIdxSubMeas_left_le
    {Question Outcome : Type*}
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι)
    (B : SubMeas Outcome ι)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1) :
    qBipartiteConsDefect ψ (averageIdxSubMeas 𝒟 A h𝒟) B ≤
      avgOver 𝒟 (fun q => qBipartiteConsDefect ψ (A q) B) := by
  have htotal := ev_opTensor_total_averageIdxSubMeas_left ψ 𝒟 A B h𝒟
  have hmatch := qBipartiteMatchMass_averageIdxSubMeas_left ψ 𝒟 A B h𝒟
  rw [qBipartiteConsDefect, htotal, hmatch]
  rw [← avgOver_sub]
  exact le_trans
    (max_zero_avgOver_le_avgOver_max_zero 𝒟
      (fun q => ev ψ (opTensor (A q).total B.total) - qBipartiteMatchMass ψ (A q) B)) <| by
        refine avgOver_mono 𝒟 _ _ ?_
        intro q
        simp [qBipartiteConsDefect]

end MIPStarRE.LDT.Pasting

end

/- Source helpers from MIPStarRE/LDT/Pasting/ComparisonLemmas/LineInterpolation/BadLine.lean. -/
/-!
# Line interpolation: bad-line event

Definitions and lemmas for `tupleInterpolatedVerticalLine` and mismatch
extraction in the line-interpolation argument.

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





lemma hRestrictionToVerticalLine_averageIdxSubMeas
    (params : Parameters) [FieldModel params.q]
    {Question : Type*}
    (u : Point params)
    (𝒟 : Distribution Question)
    (A : IdxSubMeas Question (Polynomial params.next) ι)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1) :
    hRestrictionToVerticalLine params (averageIdxSubMeas 𝒟 A h𝒟) u =
      averageIdxSubMeas 𝒟 (fun q => hRestrictionToVerticalLine params (A q) u) h𝒟 := by
  classical
  refine SubMeas.ext ?_ ?_
  · intro f
    simp [hRestrictionToVerticalLine, postprocess, averageIdxSubMeas,
      averageOperatorOverDistribution, Finset.sum_filter, Finset.sum_comm,
      Finset.smul_sum]
  · simp [hRestrictionToVerticalLine, postprocess, averageIdxSubMeas,
      averageOperatorOverDistribution]



end MIPStarRE.LDT.Pasting

end

end LIDT

open LIDT
/-!
# Line interpolation: H-B consistency error aggregation

Fixed-`u` defect, `hBConsistencyError`, degree-ratio error bounds,
and the final bad-mass aggregation lemma that drives `lem:h-b-consistency`.

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
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters) [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (strategy : _root_.LIDT.MIPStarRE.LDT.SymStrat params.next ι)
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    (k : ℕ)
    (u : _root_.LIDT.MIPStarRE.LDT.Point params) :
    _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect strategy.state
      (_root_.LIDT.MIPStarRE.LDT.Pasting.hRestrictionToVerticalLine params (_root_.LIDT.MIPStarRE.LDT.Pasting.constructedPastedSubMeas params family k) u)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.verticalLineMeasurementFamily params strategy u) ≤
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.Pasting.distinctTupleDistribution params k)
          (fun xs =>
            _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect strategy.state
              (_root_.LIDT.MIPStarRE.LDT.Pasting.hRestrictionToVerticalLine params (_root_.LIDT.MIPStarRE.LDT.Pasting.pastedInterpolationFamily params family k xs) u)
              (_root_.LIDT.MIPStarRE.LDT.Pasting.verticalLineMeasurementFamily params strategy u)) := by
  have hleft :
      _root_.LIDT.MIPStarRE.LDT.Pasting.hRestrictionToVerticalLine params (_root_.LIDT.MIPStarRE.LDT.Pasting.constructedPastedSubMeas params family k) u =
        _root_.LIDT.MIPStarRE.LDT.averageIdxSubMeas
          (_root_.LIDT.MIPStarRE.LDT.Pasting.distinctTupleDistribution params k)
          (fun xs => _root_.LIDT.MIPStarRE.LDT.Pasting.hRestrictionToVerticalLine params (
              _root_.LIDT.MIPStarRE.LDT.Pasting.pastedInterpolationFamily params family k xs) u)
          (_root_.LIDT.MIPStarRE.LDT.Pasting.distinctTupleDistribution_weight_sum_le_one params k) := by
    simpa [_root_.LIDT.MIPStarRE.LDT.Pasting.constructedPastedSubMeas] using
      _root_.LIDT.MIPStarRE.LDT.Pasting.hRestrictionToVerticalLine_averageIdxSubMeas (params := params) u
        (_root_.LIDT.MIPStarRE.LDT.Pasting.distinctTupleDistribution params k)
        (_root_.LIDT.MIPStarRE.LDT.Pasting.pastedInterpolationFamily params family k)
        (_root_.LIDT.MIPStarRE.LDT.Pasting.distinctTupleDistribution_weight_sum_le_one params k)
  rw [hleft]
  exact _root_.LIDT.MIPStarRE.LDT.Pasting.qBipartiteConsDefect_averageIdxSubMeas_left_le strategy.state
    (_root_.LIDT.MIPStarRE.LDT.Pasting.distinctTupleDistribution params k)
    (fun xs => _root_.LIDT.MIPStarRE.LDT.Pasting.hRestrictionToVerticalLine params (_root_.LIDT.MIPStarRE.LDT.Pasting.pastedInterpolationFamily params family k xs) u)
    (_root_.LIDT.MIPStarRE.LDT.Pasting.verticalLineMeasurementFamily params strategy u)
    (_root_.LIDT.MIPStarRE.LDT.Pasting.distinctTupleDistribution_weight_sum_le_one params k)
