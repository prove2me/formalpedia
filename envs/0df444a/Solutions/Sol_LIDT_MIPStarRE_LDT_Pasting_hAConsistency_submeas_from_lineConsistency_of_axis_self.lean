-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.hAConsistency_submeas_from_lineConsistency_of_axis_self
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:30:45.825986+00:00
-- url     : https://prove2.me/submissions/bbda46d6-90ba-4678-9bfe-3cb7f8364d33

-- Generated proof for MIPStarRE.LDT.Pasting.hAConsistency_submeas_from_lineConsistency_of_axis_self.
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_hAConsistency_error_le_nu_of_pos
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_pointVerticalLineSdd_of_axis_self
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_postprocess_hRestrictionToVerticalLine_eq_evaluateAt
import Theorems.Thm_LIDT_MIPStarRE_LDT_Preliminaries_consRel_uniform_equiv
import Theorems.Thm_LIDT_MIPStarRE_LDT_Preliminaries_triangleSub_right

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

/- Source helpers from MIPStarRE/LDT/Pasting/ComparisonLemmas/Common.lean. -/
/-!
# Section 12 pasting: comparison common helpers

Shared postprocessing, symmetry, distribution, boundedness, and arithmetic helpers for the Section
12 comparison lemmas.

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





lemma consRel_uniform_fst
    {α β Outcome : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β] [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (A B : IdxSubMeas α Outcome ι) (δ : Error) :
    ConsRel ψ (uniformDistribution α) A B δ →
      ConsRel ψ (uniformDistribution (α × β))
        (fun ab => A ab.1)
        (fun ab => B ab.1)
        δ := by
  intro ⟨h⟩
  constructor
  unfold bipartiteConsError at *
  calc
    avgOver (uniformDistribution (α × β))
        (fun ab => qBipartiteConsDefect ψ (A ab.1) (B ab.1))
      = avgOver (uniformDistribution α)
          (fun a => qBipartiteConsDefect ψ (A a) (B a)) := by
            exact avgOver_uniform_fst (fun a => qBipartiteConsDefect ψ (A a) (B a))
    _ ≤ δ := h

lemma qBipartiteMatchMass_nonneg
    {Outcome : Type*} [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (A B : SubMeas Outcome ι) :
    0 ≤ qBipartiteMatchMass ψ A B := by
  unfold qBipartiteMatchMass
  exact Finset.sum_nonneg fun a _ =>
    ev_nonneg_of_psd ψ _ <| opTensor_nonneg (A.outcome_pos a) (B.outcome_pos a)

lemma qBipartiteConsDefect_le_one
    {Outcome : Type*} [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (hnorm : ψ.IsNormalized)
    (A B : SubMeas Outcome ι) :
    qBipartiteConsDefect ψ A B ≤ 1 := by
  unfold qBipartiteConsDefect
  have hmatch_nonneg : 0 ≤ qBipartiteMatchMass ψ A B := qBipartiteMatchMass_nonneg ψ A B
  have htotal_le : ev ψ (opTensor A.total B.total) ≤ 1 := by
    calc
      ev ψ (opTensor A.total B.total) ≤ ev ψ (leftTensor (ι₂ := ι) A.total) := by
            exact ev_mono ψ _ _ (opTensor_le_leftTensor A.total_nonneg B.total_le_one)
      _ ≤ 1 := by
            simpa [ev_one_of_isNormalized ψ hnorm] using
              ev_mono ψ _ _ (leftTensor_le_one (ι₂ := ι) A.total_le_one)
  have hinner : ev ψ (opTensor A.total B.total) - qBipartiteMatchMass ψ A B ≤ 1 := by
    linarith
  exact max_le_iff.mpr ⟨by positivity, hinner⟩

lemma bipartiteConsError_uniform_le_one
    {Question Outcome : Type*}
    [Fintype Question] [DecidableEq Question] [Nonempty Question]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (hnorm : ψ.IsNormalized)
    (A B : IdxSubMeas Question Outcome ι) :
    bipartiteConsError ψ (uniformDistribution Question) A B ≤ 1 := by
  unfold bipartiteConsError
  exact avgOver_uniform_le_const
    (fun q => qBipartiteConsDefect ψ (A q) (B q)) (1 : Error)
    (fun q => qBipartiteConsDefect_le_one ψ hnorm (A q) (B q))

lemma qBipartiteSSCDefect_le_one
    {Outcome : Type*} [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (hnorm : ψ.IsNormalized)
    (A : SubMeas Outcome ι) :
    qBipartiteSSCDefect ψ A ≤ 1 := by
  unfold qBipartiteSSCDefect
  have hoverlap_nonneg : 0 ≤ ∑ a : Outcome, ev ψ (opTensor (A.outcome a) (A.outcome a)) := by
    exact Finset.sum_nonneg fun a _ =>
      ev_nonneg_of_psd ψ _ <| opTensor_nonneg (A.outcome_pos a) (A.outcome_pos a)
  have htotal_le : ev ψ (leftTensor (ι₂ := ι) A.total) ≤ 1 := by
    simpa [ev_one_of_isNormalized ψ hnorm] using
      ev_mono ψ _ _ (leftTensor_le_one (ι₂ := ι) A.total_le_one)
  have hinner : ev ψ (leftTensor (ι₂ := ι) A.total) -
      ∑ a : Outcome, ev ψ (opTensor (A.outcome a) (A.outcome a)) ≤ 1 := by
    linarith
  exact max_le_iff.mpr ⟨by positivity, hinner⟩

lemma bipartiteSSCError_uniform_le_one
    {Question Outcome : Type*}
    [Fintype Question] [DecidableEq Question] [Nonempty Question]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (hnorm : ψ.IsNormalized)
    (A : IdxSubMeas Question Outcome ι) :
    bipartiteSSCError ψ (uniformDistribution Question) A ≤ 1 := by
  unfold bipartiteSSCError
  exact avgOver_uniform_le_const
    (fun q => qBipartiteSSCDefect ψ (A q)) (1 : Error)
    (fun q => qBipartiteSSCDefect_le_one ψ hnorm (A q))







end MIPStarRE.LDT.Pasting

end

/- Source helpers from MIPStarRE/LDT/Pasting/Core/LdGbcon.lean. -/
/-!
# Section 12 pasting: vertical-line consistency transfer

The `ldGbcon` transfer compares the slice family `G^x` with the vertical-line
answers `B^u`.  It combines the conditioned axis-parallel consistency estimate
with the point-to-vertical-line state-dependent-distance bound.
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]











/-- Named submeasurement-family form of `pointVerticalLineSdd_of_axis_self`.

The proof above constructs the vertical-line measurement as a complete
measurement-valued family.  The degree-zero estimates use only its underlying
submeasurement family, namely `liftedVerticalLineAnswerFamily`. -/
theorem pointVerticalLineSdd_liftedVerticalLine_of_axis_self
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta : Error)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself : strategy.selfConsistencyFailureProbability ≤ delta) :
    SDDRel strategy.state
      (uniformDistribution (Point params.next))
      (IdxSubMeas.liftRight (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
      (IdxSubMeas.liftRight (liftedVerticalLineAnswerFamily params strategy))
      (8 * (params.m : Error) * eps + 4 * delta) := by
  change SDDRel strategy.state
    (uniformDistribution (Point params.next))
    (IdxSubMeas.liftRight (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
    (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas (ldGbconVerticalLineMeasurement params strategy)))
    (8 * (params.m : Error) * eps + 4 * delta)
  exact pointVerticalLineSdd_of_axis_self params strategy eps delta haxis hself











end MIPStarRE.LDT.Pasting

end

end LIDT

open LIDT
/-!
# Section 12 pasting: H-A consistency

Vertical-line to point-consistency transport and completed-measurement statement for
`cor:h-a-consistency`.

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
    (H : _root_.LIDT.MIPStarRE.LDT.SubMeas (_root_.LIDT.MIPStarRE.LDT.Polynomial params.next) ι)
    (eps delta gamma zeta : _root_.LIDT.MIPStarRE.LDT.Error)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself_good : strategy.selfConsistencyFailureProbability ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta)
    (k : ℕ)
    (hk_pos : 1 ≤ k)
    (hline :
      _root_.LIDT.MIPStarRE.LDT.ConsRel strategy.state (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params))
        (_root_.LIDT.MIPStarRE.LDT.Pasting.hRestrictionToVerticalLine params H)
        (_root_.LIDT.MIPStarRE.LDT.Pasting.verticalLineMeasurementFamily params strategy)
        (_root_.LIDT.MIPStarRE.LDT.Pasting.hBConsistencyError params eps delta gamma zeta k)) :
    _root_.LIDT.MIPStarRE.LDT.ConsRel strategy.state (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
        (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params.next H)
        (_root_.LIDT.MIPStarRE.LDT.MainInductionStep.ldPastingInInductionNu params k
          eps delta gamma zeta) := by
  let pointLineMeas : _root_.LIDT.MIPStarRE.LDT.IdxMeas (_root_.LIDT.MIPStarRE.LDT.Point params.next) (_root_.LIDT.MIPStarRE.LDT.Fq params.next) ι := fun u =>
    { toSubMeas := _root_.LIDT.MIPStarRE.LDT.Pasting.liftedVerticalLineAnswerFamily params strategy u
      total_eq_one :=
        (strategy.axisParallelMeasurement
          { base := _root_.LIDT.MIPStarRE.LDT.appendPoint params (_root_.LIDT.MIPStarRE.LDT.truncatePoint params u) _root_.LIDT.MIPStarRE.LDT.zeroCoord
            direction := _root_.LIDT.MIPStarRE.LDT.lastCoord params }).total_eq_one }
  let pointMeas : _root_.LIDT.MIPStarRE.LDT.IdxMeas (_root_.LIDT.MIPStarRE.LDT.Point params.next) (_root_.LIDT.MIPStarRE.LDT.Fq params.next) ι :=
    fun u => (strategy.pointMeasurement u).toMeasurement
  let νB := _root_.LIDT.MIPStarRE.LDT.Pasting.hBConsistencyError params eps delta gamma zeta k
  let ν := _root_.LIDT.MIPStarRE.LDT.MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta
  let eps' : _root_.LIDT.MIPStarRE.LDT.Error := min eps 1
  let delta' : _root_.LIDT.MIPStarRE.LDT.Error := min delta 1
  have haxis_le_one : strategy.axisParallelFailureProbability ≤ 1 := by
    simpa [_root_.LIDT.MIPStarRE.LDT.SymStrat.axisParallelFailureProbability] using
      _root_.LIDT.MIPStarRE.LDT.Pasting.bipartiteConsError_uniform_le_one strategy.state strategy.isNormalized
        (_root_.LIDT.MIPStarRE.LDT.axisParallelPointAnswerFamily strategy)
        (_root_.LIDT.MIPStarRE.LDT.axisParallelLineAnswerFamily strategy)
  have hself_le_one : strategy.selfConsistencyFailureProbability ≤ 1 := by
    simpa [_root_.LIDT.MIPStarRE.LDT.SymStrat.selfConsistencyFailureProbability] using
      _root_.LIDT.MIPStarRE.LDT.Pasting.bipartiteSSCError_uniform_le_one strategy.state strategy.isNormalized
        (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
  have haxis_small : strategy.axisParallelFailureProbability ≤ eps' :=
    le_min haxis haxis_le_one
  have hself_small : strategy.selfConsistencyFailureProbability ≤ delta' :=
    le_min hself_good hself_le_one
  have heps_nonneg : 0 ≤ eps := by
    exact le_trans
      (_root_.LIDT.MIPStarRE.LDT.bipartiteConsError_nonneg strategy.state
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.AxisParallelTestSample params.next))
        (_root_.LIDT.MIPStarRE.LDT.axisParallelPointAnswerFamily strategy)
        (_root_.LIDT.MIPStarRE.LDT.axisParallelLineAnswerFamily strategy))
      haxis
  have hdelta_nonneg : 0 ≤ delta := by
    exact le_trans
      (_root_.LIDT.MIPStarRE.LDT.bipartiteSSCError_nonneg strategy.state
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
        (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
      hself_good
  have hline_prod :
      _root_.LIDT.MIPStarRE.LDT.ConsRel strategy.state (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.VerticalLineQuestion params × _root_.LIDT.MIPStarRE.LDT.Fq params))
        (fun ux => _root_.LIDT.MIPStarRE.LDT.Pasting.hRestrictionToVerticalLine params H ux.1)
        (fun ux => _root_.LIDT.MIPStarRE.LDT.Pasting.verticalLineMeasurementFamily params strategy ux.1)
        νB := by
    exact _root_.LIDT.MIPStarRE.LDT.Pasting.consRel_uniform_fst strategy.state
      (_root_.LIDT.MIPStarRE.LDT.Pasting.hRestrictionToVerticalLine params H)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.verticalLineMeasurementFamily params strategy)
      νB
      hline
  have hline_next :
      _root_.LIDT.MIPStarRE.LDT.ConsRel strategy.state (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
        (fun u => _root_.LIDT.MIPStarRE.LDT.Pasting.hRestrictionToVerticalLine params H (_root_.LIDT.MIPStarRE.LDT.truncatePoint params u))
        (fun u => _root_.LIDT.MIPStarRE.LDT.Pasting.verticalLineMeasurementFamily params strategy (_root_.LIDT.MIPStarRE.LDT.truncatePoint params u))
        νB := by
    exact (_root_.LIDT.MIPStarRE.LDT.Preliminaries.consRel_uniform_equiv
      ((_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointNextEquiv params).symm)
      strategy.state
      (fun ux => _root_.LIDT.MIPStarRE.LDT.Pasting.hRestrictionToVerticalLine params H ux.1)
      (fun ux => _root_.LIDT.MIPStarRE.LDT.Pasting.verticalLineMeasurementFamily params strategy ux.1)
      νB).1 hline_prod
  have hline_point :
      _root_.LIDT.MIPStarRE.LDT.ConsRel strategy.state (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
        (_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params.next H)
        (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas pointLineMeas)
        νB := by
    have hproc :=
      _root_.LIDT.MIPStarRE.LDT.Preliminaries.consRelDataProcessing_questionDependent strategy.state
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
        (fun u => _root_.LIDT.MIPStarRE.LDT.Pasting.hRestrictionToVerticalLine params H (_root_.LIDT.MIPStarRE.LDT.truncatePoint params u))
        (fun u => _root_.LIDT.MIPStarRE.LDT.Pasting.verticalLineMeasurementFamily params strategy (_root_.LIDT.MIPStarRE.LDT.truncatePoint params u))
        νB
        (fun u f => f (_root_.LIDT.MIPStarRE.LDT.pointHeight params u))
        hline_next
    have hleft :
        (fun u : _root_.LIDT.MIPStarRE.LDT.Point params.next =>
          _root_.LIDT.MIPStarRE.LDT.postprocess
            (_root_.LIDT.MIPStarRE.LDT.Pasting.hRestrictionToVerticalLine params H (_root_.LIDT.MIPStarRE.LDT.truncatePoint params u))
            (fun f => f (_root_.LIDT.MIPStarRE.LDT.pointHeight params u))) =
          (fun u => _root_.LIDT.MIPStarRE.LDT.evaluateAt params.next u H) := by
      funext u
      exact _root_.LIDT.MIPStarRE.LDT.Pasting.postprocess_hRestrictionToVerticalLine_eq_evaluateAt params H u
    rw [hleft] at hproc
    change _root_.LIDT.MIPStarRE.LDT.ConsRel strategy.state (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
      (fun u => _root_.LIDT.MIPStarRE.LDT.evaluateAt params.next u H)
      (fun u =>
        _root_.LIDT.MIPStarRE.LDT.postprocess
          (_root_.LIDT.MIPStarRE.LDT.Pasting.verticalLineMeasurementFamily params strategy (_root_.LIDT.MIPStarRE.LDT.truncatePoint params u))
          (fun f => f (_root_.LIDT.MIPStarRE.LDT.pointHeight params u)))
      νB
    exact hproc
  have hpoint_sdd :
      _root_.LIDT.MIPStarRE.LDT.SDDRel strategy.state
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
      (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas pointLineMeas))
      (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas pointMeas))
      (8 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * eps' + 4 * delta') := by
    have hpublic :=
      _root_.LIDT.MIPStarRE.LDT.Pasting.pointVerticalLineSdd_liftedVerticalLine_of_axis_self
        params strategy eps' delta' haxis_small hself_small
    have hline_eq :
        _root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas pointLineMeas =
          _root_.LIDT.MIPStarRE.LDT.Pasting.liftedVerticalLineAnswerFamily params strategy := by
      funext u
      rfl
    have hpoint_eq :
        _root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas pointMeas =
          _root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas strategy.pointMeasurement := by
      funext u
      rfl
    rw [hline_eq, hpoint_eq]
    exact _root_.LIDT.MIPStarRE.LDT.Preliminaries.sddRel_symm strategy.state
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next)) _ _ _ hpublic
  have htri :
      _root_.LIDT.MIPStarRE.LDT.ConsRel strategy.state (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
        (_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params.next H)
        (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (νB + Real.sqrt (8 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * eps' + 4 * delta')) := by
    exact _root_.LIDT.MIPStarRE.LDT.Preliminaries.triangleSub_right strategy.state
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
      strategy.isNormalized
      (by simpa using _root_.LIDT.MIPStarRE.LDT.uniformDistribution_weight_sum_le_one (_root_.LIDT.MIPStarRE.LDT.Point params.next))
      (_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params.next H)
      pointLineMeas
      pointMeas
      νB
      (8 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * eps' + 4 * delta')
      hline_point
      hpoint_sdd
  have hswap :
      _root_.LIDT.MIPStarRE.LDT.ConsRel strategy.state (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
        (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params.next H)
        (νB + Real.sqrt (8 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * eps' + 4 * delta')) := by
    exact _root_.LIDT.MIPStarRE.LDT.consRel_symm_of_density_fixed strategy.state strategy.densityFixed
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
      (_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params.next H)
      (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (νB + Real.sqrt (8 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * eps' + 4 * delta'))
      htri
  refine ⟨?_⟩
  calc
    _root_.LIDT.MIPStarRE.LDT.bipartiteConsError strategy.state (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
        (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params.next H)
      ≤ νB + Real.sqrt (8 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * eps' + 4 * delta') := hswap.offDiagonalBound
    _ ≤ ν := by
      exact _root_.LIDT.MIPStarRE.LDT.Pasting.hAConsistency_error_le_nu_of_pos params eps delta gamma zeta k hk_pos
        heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg
