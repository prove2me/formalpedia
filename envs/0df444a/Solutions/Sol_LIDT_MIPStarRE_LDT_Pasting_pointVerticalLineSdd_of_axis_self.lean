-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.pointVerticalLineSdd_of_axis_self
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:26:51.978024+00:00
-- url     : https://prove2.me/submissions/db77c70c-a051-4687-985f-a9ec898455f4

-- Generated proof for MIPStarRE.LDT.Pasting.pointVerticalLineSdd_of_axis_self.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Core_LdGbcon
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Tuples
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_GHatSandwich
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_PastedFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_Switcheroo
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Local
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
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
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_verticalLine_pointAt_appendPoint
import Theorems.Thm_LIDT_MIPStarRE_LDT_Preliminaries_bipartiteSSCRel_of_consRel_self_measurement
import Theorems.Thm_LIDT_MIPStarRE_LDT_Preliminaries_otherTwoNotionsOfSelfConsistency

namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

namespace LIDT

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





private lemma ldGbconAxisLineMeasurement_eq_verticalLineMeasurement
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) :
    IdxMeas.toIdxSubMeas (ldGbconAxisLineMeasurement params strategy) =
      IdxMeas.toIdxSubMeas (ldGbconVerticalLineMeasurement params strategy) := by
  funext u
  refine SubMeas.ext (A := (ldGbconAxisLineMeasurement params strategy u).toSubMeas)
    (B := (ldGbconVerticalLineMeasurement params strategy u).toSubMeas) ?_ ?_
  · intro a
    let ℓ : AxisParallelLine params.next :=
      { base := appendPoint params (truncatePoint params u) zeroCoord
      , direction := lastCoord params }
    have hrebased :
        AxisParallelLine.rebaseAt ℓ (pointHeight params u) =
          { base := u, direction := lastCoord params } := by
      have happend : appendPoint params (truncatePoint params u) (pointHeight params u) = u := by
        exact (pointNextEquiv params).left_inv u
      have hbase : ℓ.pointAt (pointHeight params u) = u := by
        calc
          ℓ.pointAt (pointHeight params u)
            = appendPoint params (truncatePoint params u) (pointHeight params u) := by
                simpa [ℓ] using
                  verticalLine_pointAt_appendPoint params
                    (truncatePoint params u) (pointHeight params u)
          _ = u := happend
      simpa [AxisParallelLine.rebaseAt, ℓ] using
        congrArg
          (fun base : Point params.next =>
            ({ base := base, direction := lastCoord params } : AxisParallelLine params.next))
          hbase
    calc
      (ldGbconAxisLineMeasurement params strategy u).toSubMeas.outcome a
        = (postprocess
            ((strategy.axisParallelMeasurement
              (AxisParallelLine.rebaseAt ℓ (pointHeight params u))).toSubMeas)
            (· zeroCoord)).outcome a := by
              simp [ldGbconAxisLineMeasurement, hrebased, ℓ]
      _ = (postprocess ((strategy.axisParallelMeasurement ℓ).toSubMeas)
            (fun f => f (pointHeight params u))).outcome a := by
              exact AxisParallelCovariantMeasurement.reparamInvariant
                strategy.axisParallelMeasurement ℓ (pointHeight params u) a
      _ = (ldGbconVerticalLineMeasurement params strategy u).toSubMeas.outcome a := by
            rfl
  · have hA : (ldGbconAxisLineMeasurement params strategy u).toSubMeas.total = 1 := by
        let ℓ : AxisParallelLine params.next := { base := u, direction := lastCoord params }
        have hA' :
            (postprocess ((strategy.axisParallelMeasurement ℓ).toSubMeas) (· zeroCoord)).total =
              1 := by
          simpa [postprocess_total] using (strategy.axisParallelMeasurement ℓ).total_eq_one
        change
          (postprocess ((strategy.axisParallelMeasurement ℓ).toSubMeas)
            (fun f => f zeroCoord)).total = 1
        exact hA'
    have hB : (ldGbconVerticalLineMeasurement params strategy u).toSubMeas.total = 1 := by
        let ℓ : AxisParallelLine params.next :=
          { base := appendPoint params (truncatePoint params u) zeroCoord
          , direction := lastCoord params }
        have hB' :
            (postprocess (verticalLineMeasurementFamily params strategy (truncatePoint params u))
              (fun f => f (pointHeight params u))).total = 1 := by
          simpa [verticalLineMeasurementFamily, ℓ, postprocess_total] using
            (strategy.axisParallelMeasurement ℓ).total_eq_one
        change
          (postprocess (verticalLineMeasurementFamily params strategy (truncatePoint params u))
            (fun f => f (pointHeight params u))).total = 1
        exact hB'
    rw [hA, hB]

private lemma ldGbcon_axis_last_direction_consistency
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps : Error)
    (haxis : ConsRel strategy.state
      (uniformDistribution (AxisParallelTestSample params.next))
      (axisParallelPointAnswerFamily strategy)
      (axisParallelLineAnswerFamily strategy)
      eps) :
    ConsRel strategy.state
      (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (IdxMeas.toIdxSubMeas (ldGbconAxisLineMeasurement params strategy))
      ((params.next.m : Error) * eps) := by
  let err : AxisParallelTestSample params.next → Error := fun s =>
    qBipartiteConsDefect strategy.state
      (axisParallelPointAnswerFamily strategy s)
      (axisParallelLineAnswerFamily strategy s)
  have hpointwise :
      ∀ u,
        err (u, lastCoord params) ≤
          (params.next.m : Error) *
            avgOver (uniformDistribution (Fin params.next.m)) (fun i => err (u, i)) := by
    intro u
    let S : Finset (Fin params.next.m) := {lastCoord params}
    have hsingle : Finset.sum S (fun i => err (u, i)) = err (u, lastCoord params) := by
      simp [S, err]
    have hsum_ge : err (u, lastCoord params) ≤ ∑ i : Fin params.next.m, err (u, i) := by
      calc
        err (u, lastCoord params) = Finset.sum S (fun i => err (u, i)) := by
              symm
              exact hsingle
        _ ≤ ∑ i : Fin params.next.m, err (u, i) := by
              refine Finset.sum_le_sum_of_subset_of_nonneg (by simp) ?_
              intro i _ _
              exact qBipartiteConsDefect_nonneg strategy.state
                (axisParallelPointAnswerFamily strategy (u, i))
                (axisParallelLineAnswerFamily strategy (u, i))
    have hm : ((params.next.m : ℕ) : Error) ≠ 0 := by
      simpa [Parameters.next] using
        (show (((params.m + 1 : ℕ)) : Error) ≠ 0 by
          exact_mod_cast Nat.succ_ne_zero params.m)
    have havg_eq :
        (params.next.m : Error) *
            avgOver (uniformDistribution (Fin params.next.m)) (fun i => err (u, i)) =
          ∑ i : Fin params.next.m, err (u, i) := by
      calc
        (params.next.m : Error) *
            avgOver (uniformDistribution (Fin params.next.m)) (fun i => err (u, i))
          = (params.next.m : Error) *
              ∑ i : Fin params.next.m, (1 / (params.next.m : Error)) * err (u, i) := by
                simp [avgOver, uniformDistribution, Fintype.card_fin]
        _ = ∑ i : Fin params.next.m,
              ((params.next.m : Error) * (1 / (params.next.m : Error))) * err (u, i) := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl ?_
                intro i _
                ring
        _ = ∑ i : Fin params.next.m, err (u, i) := by
              refine Finset.sum_congr rfl ?_
              intro i _
              field_simp [hm]
    nlinarith [hsum_ge, havg_eq]
  rcases haxis with ⟨haxis⟩
  refine ⟨?_⟩
  unfold bipartiteConsError at *
  change
    avgOver (uniformDistribution (Point params.next)) (fun u =>
      qBipartiteConsDefect strategy.state
        (axisParallelPointAnswerFamily strategy (u, lastCoord params))
        (axisParallelLineAnswerFamily strategy (u, lastCoord params))) ≤
      (params.next.m : Error) * eps
  exact
    calc
      avgOver (uniformDistribution (Point params.next)) (fun u =>
        qBipartiteConsDefect strategy.state
            (axisParallelPointAnswerFamily strategy (u, lastCoord params))
            (axisParallelLineAnswerFamily strategy (u, lastCoord params)))
        ≤ avgOver (uniformDistribution (Point params.next)) (fun u =>
            (params.next.m : Error) *
              avgOver (uniformDistribution (Fin params.next.m)) (fun i => err (u, i))) := by
                exact avgOver_mono _ _ _ hpointwise
      _ = (params.next.m : Error) *
            avgOver (uniformDistribution (Point params.next)) (fun u =>
              avgOver (uniformDistribution (Fin params.next.m)) (fun i => err (u, i))) := by
                rw [avgOver_const_mul]
      _ = (params.next.m : Error) *
            avgOver (uniformDistribution (AxisParallelTestSample params.next)) err := by
            rw [← avgOver_uniform_prod (f := fun u i => err (u, i))]
      _ ≤ (params.next.m : Error) * eps := by
            exact mul_le_mul_of_nonneg_left haxis (by positivity)















end MIPStarRE.LDT.Pasting

end

/- Source helpers from MIPStarRE/LDT/Preliminaries/SelfConsistency/Core.lean. -/
/-!
# Self-consistency: core squared-mass bounds

Squared-mass lower bound lemma derived from bipartite self-consistency on
permutation-invariant states (`prop:cool-prop`).

## References

- `references/ldt-paper/preliminaries.tex`
- `blueprint/src/chapter/ch03_preliminaries.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT









/-- For full measurements, bipartite SSC and diagonal self-consistency are
equivalent. -/
theorem bipartiteSSCRel_iff_consRel_self_measurement {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (𝒟 : Distribution Question)
    (A : IdxMeas Question Outcome ι) (δ : Error) :
    BipartiteSSCRel ψ 𝒟 (IdxMeas.toIdxSubMeas A) δ ↔
      @ConsRel Question Outcome ι ι _ _ _ _ _ ψ 𝒟
        (IdxMeas.toIdxSubMeas A) (IdxMeas.toIdxSubMeas A) δ := by
  constructor
  · exact otherTwoNotionsOfSelfConsistency ψ 𝒟 (IdxMeas.toIdxSubMeas A) δ
  · exact bipartiteSSCRel_of_consRel_self_measurement ψ 𝒟 A δ

end MIPStarRE.LDT.Preliminaries

end

end LIDT

open LIDT
/-!
# Section 12 pasting: vertical-line consistency transfer

The `ldGbcon` transfer compares the slice family `G^x` with the vertical-line
answers `B^u`.  It combines the conditioned axis-parallel consistency estimate
with the point-to-vertical-line state-dependent-distance bound.
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
    (eps delta : _root_.LIDT.MIPStarRE.LDT.Error)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself : strategy.selfConsistencyFailureProbability ≤ delta) :
    _root_.LIDT.MIPStarRE.LDT.SDDRel strategy.state
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
      (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
      (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas (_root_.LIDT.MIPStarRE.LDT.Pasting.ldGbconVerticalLineMeasurement params strategy)))
      (8 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * eps + 4 * delta) := by
  let pointMeas : _root_.LIDT.MIPStarRE.LDT.IdxMeas (_root_.LIDT.MIPStarRE.LDT.Point params.next) (_root_.LIDT.MIPStarRE.LDT.Fq params.next) ι :=
    _root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxMeas strategy.pointMeasurement
  have hpointMeas_sub :
      _root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas pointMeas =
        _root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas strategy.pointMeasurement := by
    funext u
    rfl
  have haxis_all : _root_.LIDT.MIPStarRE.LDT.ConsRel strategy.state
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.AxisParallelTestSample params.next))
      (_root_.LIDT.MIPStarRE.LDT.axisParallelPointAnswerFamily strategy)
      (_root_.LIDT.MIPStarRE.LDT.axisParallelLineAnswerFamily strategy)
      eps := ⟨haxis⟩
  have hself_cons : _root_.LIDT.MIPStarRE.LDT.ConsRel strategy.state
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
      (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      delta :=
    let hself_rel :
        _root_.LIDT.MIPStarRE.LDT.BipartiteSSCRel strategy.state
          (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
          (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas pointMeas)
          delta :=
      ⟨by rw [hpointMeas_sub]; exact hself⟩
    let hcons :=
      (_root_.LIDT.MIPStarRE.LDT.Preliminaries.bipartiteSSCRel_iff_consRel_self_measurement strategy.state
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next)) pointMeas delta).mp hself_rel
    hpointMeas_sub ▸ hcons
  have heps_nonneg : 0 ≤ eps := by
    exact le_trans
      (_root_.LIDT.MIPStarRE.LDT.bipartiteConsError_nonneg strategy.state
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.AxisParallelTestSample params.next))
        (_root_.LIDT.MIPStarRE.LDT.axisParallelPointAnswerFamily strategy)
        (_root_.LIDT.MIPStarRE.LDT.axisParallelLineAnswerFamily strategy))
      haxis
  have hnext_le_two_m_nat : params.next.m ≤ 2 * params.m := by
    have hm_nat : 1 ≤ params.m := Nat.succ_le_of_lt params.hm
    have : params.m + 1 ≤ 2 * params.m := by omega
    simpa [_root_.LIDT.MIPStarRE.LDT.Parameters.next] using this
  have hnext_le_two_m : (params.next.m : _root_.LIDT.MIPStarRE.LDT.Error) ≤ 2 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) := by
    exact_mod_cast hnext_le_two_m_nat
  have haxis_last : _root_.LIDT.MIPStarRE.LDT.ConsRel strategy.state
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
      (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas (ldGbconAxisLineMeasurement params strategy))
      ((params.next.m : _root_.LIDT.MIPStarRE.LDT.Error) * eps) :=
    ldGbcon_axis_last_direction_consistency params strategy eps haxis_all
  have haxis_bip :=
    _root_.LIDT.MIPStarRE.LDT.Preliminaries.simeqToApprox strategy.state (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
      pointMeas
      (ldGbconAxisLineMeasurement params strategy)
      ((params.next.m : _root_.LIDT.MIPStarRE.LDT.Error) * eps)
      (by rwa [hpointMeas_sub])
  have haxis_sdd : _root_.LIDT.MIPStarRE.LDT.SDDRel strategy.state
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
      (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
      (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas (ldGbconAxisLineMeasurement params strategy)))
      (4 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * eps) := by
        refine _root_.LIDT.MIPStarRE.LDT.Preliminaries.stateDependentDistanceRel_mono strategy.state
          (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
          (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
          (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas (ldGbconAxisLineMeasurement params strategy)))
          (2 * ((params.next.m : _root_.LIDT.MIPStarRE.LDT.Error) * eps)) (4 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * eps) ?_ ?_
        · have hmule : ((params.next.m : _root_.LIDT.MIPStarRE.LDT.Error) * eps) ≤ (2 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error)) * eps := by
            exact mul_le_mul_of_nonneg_right hnext_le_two_m heps_nonneg
          nlinarith
        · exact ⟨haxis_bip.leftRightSquaredDistanceBound⟩
  have hself_sdd : _root_.LIDT.MIPStarRE.LDT.SDDRel strategy.state
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
      (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
      (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
      (2 * delta) := by
        exact ⟨(_root_.LIDT.MIPStarRE.LDT.Preliminaries.simeqToApprox strategy.state
          (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next)) pointMeas pointMeas delta
          (by rwa [hpointMeas_sub])).leftRightSquaredDistanceBound⟩
  have hself_sdd_symm : _root_.LIDT.MIPStarRE.LDT.SDDRel strategy.state
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
      (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
      (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
      (2 * delta) := by
        exact _root_.LIDT.MIPStarRE.LDT.Preliminaries.sddRel_symm strategy.state
          (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next)) _ _ _ hself_sdd
  have hpoint_to_axis_raw : _root_.LIDT.MIPStarRE.LDT.SDDRel strategy.state
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
      (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
      (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas (ldGbconAxisLineMeasurement params strategy)))
      (2 * ((2 * delta) + (4 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * eps))) := by
        exact _root_.LIDT.MIPStarRE.LDT.Preliminaries.stateDependentDistanceRel_triangle strategy.state
          (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
          (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
          (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
          (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas (ldGbconAxisLineMeasurement params strategy)))
          (2 * delta) (4 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * eps)
          hself_sdd_symm haxis_sdd
  have hpoint_to_axis : _root_.LIDT.MIPStarRE.LDT.SDDRel strategy.state
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
      (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
      (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas (ldGbconAxisLineMeasurement params strategy)))
      (8 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * eps + 4 * delta) := by
        refine _root_.LIDT.MIPStarRE.LDT.Preliminaries.stateDependentDistanceRel_mono strategy.state
          (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
          (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
          (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas (ldGbconAxisLineMeasurement params strategy)))
          (2 * ((2 * delta) + (4 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * eps)))
          (8 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * eps + 4 * delta) ?_ hpoint_to_axis_raw
        ring_nf
        exact le_rfl
  have hlift :
      _root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas
          (ldGbconAxisLineMeasurement params strategy)) =
        _root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas
          (_root_.LIDT.MIPStarRE.LDT.Pasting.ldGbconVerticalLineMeasurement params strategy)) := by
    rw [ldGbconAxisLineMeasurement_eq_verticalLineMeasurement params strategy]
  exact hlift ▸ hpoint_to_axis
