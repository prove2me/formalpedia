-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.CommutativityPoints.sampledDiagonalLineApproximation_pointWithDiagonalLine
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T14:08:57.898105+00:00
-- url     : https://prove2.me/submissions/ec99037a-cf0a-4bcd-b18b-5e0e72de910a

-- Generated proof for MIPStarRE.LDT.CommutativityPoints.sampledDiagonalLineApproximation_pointWithDiagonalLine.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
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
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyFailures
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

namespace LIDT

/- Source helpers from MIPStarRE/LDT/CommutativityPoints/Approximation.lean. -/
/-!
# Section 10 — commutativity points approximation layer

Restricted-diagonal approximation infrastructure for commutativity at points.
-/

@[expose] public section

namespace MIPStarRE.LDT.CommutativityPoints

open MIPStarRE.LDT.GlobalVariance (PointPairQuestion)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped _root_.Matrix MatrixOrder ComplexOrder BigOperators























/-- Consistency transfer for the corrected diagonal branch at the final
restriction index.

The corrected test samples a restricted diagonal line and compares the point
measurement at its distinguished base point with the diagonal measurement
postprocessed by evaluation at `zeroCoord`. The global diagonal-line test bound
therefore controls this last restricted slice in particular. -/
private lemma sampledDiagonalLineConsistency
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    ConsRel strategy.state
      (uniformDistribution (RestrictedDiagonalSample params (lastRestrictionIndex params)))
      (diagonalPointAnswerFamily strategy (lastRestrictionIndex params))
      (rawDiagonalLineAnswerFamily params strategy (lastRestrictionIndex params))
      (restrictedDiagonalLinesConsistencyError
        params gamma) := by
  let j := lastRestrictionIndex params
  let err : Fin params.m → Error := fun j =>
    bipartiteConsError strategy.state
      (uniformDistribution (RestrictedDiagonalSample params j))
      (diagonalPointAnswerFamily strategy j)
      (rawDiagonalLineAnswerFamily params strategy j)
  have herr_nonneg : ∀ j : Fin params.m, 0 ≤ err j := by
    intro j'
    exact bipartiteConsError_nonneg strategy.state
      (uniformDistribution (RestrictedDiagonalSample params j'))
      (diagonalPointAnswerFamily strategy j')
      (rawDiagonalLineAnswerFamily params strategy j')
  have hsum_bound : ∑ j' : Fin params.m, err j' ≤ gamma * (params.m : Error) := by
    have hm_nonneg : 0 ≤ (params.m : Error) := by
      positivity
    have hm_ne : (params.m : Error) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt params.hm
    have hdiag := hgood.diagonalLineTest
    dsimp [SymStrat.diagonalFailureProbability, err] at hdiag
    calc
      ∑ j' : Fin params.m, err j'
        = (params.m : Error) * ((1 / (params.m : Error)) * ∑ j' : Fin params.m, err j') := by
            field_simp [hm_ne]
      _ ≤ (params.m : Error) * gamma := by
            exact mul_le_mul_of_nonneg_left hdiag hm_nonneg
      _ = gamma * (params.m : Error) := by ring
  have hj_le : err j ≤ gamma * (params.m : Error) := by
    calc
      err j ≤ ∑ j' : Fin params.m, err j' := by
        exact Finset.single_le_sum (fun j' _ => herr_nonneg j') (Finset.mem_univ j)
      _ ≤ gamma * (params.m : Error) := hsum_bound
  refine ⟨?_⟩
  simpa [j, err, restrictedDiagonalLinesConsistencyError] using hj_le

/-- Convert the corrected restricted diagonal consistency estimate into the
corresponding SDD approximation bound.

This is the final-slice version of the diagonal branch that feeds the
commutativity-at-points argument. It packages the consistency estimate through
`Preliminaries.simeqToApprox`. -/
private lemma sampledDiagonalLineApproximation
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    SDDRel strategy.state
      (uniformDistribution (RestrictedDiagonalSample params (lastRestrictionIndex params)))
      (IdxSubMeas.liftLeft
        (diagonalPointAnswerFamily strategy (lastRestrictionIndex params)))
      (IdxSubMeas.liftRight
        (rawDiagonalLineAnswerFamily params strategy (lastRestrictionIndex params)))
      (pointDiagonalLineApproxError params gamma) := by
  let j := lastRestrictionIndex params
  let pointFamily : IdxMeas (RestrictedDiagonalSample params j) (Fq params) ι :=
    fun s => (strategy.pointMeasurement s.1).toMeasurement
  let lineFamily : IdxMeas (RestrictedDiagonalSample params j) (Fq params) ι :=
    fun s =>
      { toSubMeas := rawDiagonalLineAnswerFamily params strategy j s
        total_eq_one :=
          calc
            (rawDiagonalLineAnswerFamily params strategy j s).total =
                ((strategy.diagonalMeasurement
                  { base := s.1
                    direction := extendRestrictedDirection j s.2 }).toSubMeas).total := by
              dsimp [rawDiagonalLineAnswerFamily]
              rw [postprocess_total]
            _ = 1 :=
              (strategy.diagonalMeasurement
                { base := s.1
                  direction := extendRestrictedDirection j s.2 }).total_eq_one }
  have hcons := sampledDiagonalLineConsistency params strategy eps delta gamma hgood
  have hcons' :
      ConsRel strategy.state
        (uniformDistribution (RestrictedDiagonalSample params j))
        (IdxMeas.toIdxSubMeas pointFamily)
        (IdxMeas.toIdxSubMeas lineFamily)
        (restrictedDiagonalLinesConsistencyError params gamma) := by
    change ConsRel strategy.state
      (uniformDistribution (RestrictedDiagonalSample params (lastRestrictionIndex params)))
      (diagonalPointAnswerFamilyOf strategy.pointMeasurement (lastRestrictionIndex params))
      (rawDiagonalLineAnswerFamily params strategy (lastRestrictionIndex params))
      (restrictedDiagonalLinesConsistencyError params gamma)
    exact hcons
  have happrox :
      Preliminaries.BipartiteSDDRel strategy.state
        (uniformDistribution (RestrictedDiagonalSample params j))
        (IdxMeas.toIdxSubMeas pointFamily)
        (IdxMeas.toIdxSubMeas lineFamily)
        (2 * restrictedDiagonalLinesConsistencyError params gamma) :=
    Preliminaries.simeqToApprox strategy.state
      (uniformDistribution (RestrictedDiagonalSample params j))
      pointFamily lineFamily
      (restrictedDiagonalLinesConsistencyError params gamma) hcons'
  refine ⟨?_⟩
  simpa [j, pointFamily, lineFamily, diagonalPointAnswerFamily,
    pointDiagonalLineApproxError, restrictedDiagonalLinesConsistencyError,
    Preliminaries.BipartiteSDDRel, sddError, IdxMeas.toIdxSubMeas,
    IdxSubMeas.liftLeft, IdxSubMeas.liftRight] using
    happrox.leftRightSquaredDistanceBound











end MIPStarRE.LDT.CommutativityPoints

end

/- Source helpers from MIPStarRE/LDT/Test/StrategyCore.lean. -/
/-!
# Section 3 — Strategy core

Base state-invariance and strategy structures for the low individual degree test.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT







































namespace AxisParallelLine





end AxisParallelLine

namespace DiagonalLine



/-- Evaluating a transported diagonal-line measurement at `zeroCoord` agrees with
reading the original measurement at the rebasing parameter. -/
theorem transportMeasurement_postprocess_zero
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ProjMeas (DiagonalLinePolynomial params) ι) (t a : Fq params) :
    (postprocess (transportMeasurement (params := params) M t).toSubMeas
        (· zeroCoord)).outcome a =
      (postprocess M.toSubMeas (fun f => f t)).outcome a := by
  have h :=
    SubMeas.postprocess_transport
      (e := DiagonalLinePolynomial.reparamAtEquiv (params := params) t)
      (A := M.toSubMeas)
      (f := fun g : DiagonalLinePolynomial params => g zeroCoord)
  simpa [transportMeasurement, DiagonalLinePolynomial.reparamAtEquiv,
    DiagonalLinePolynomial.reparamAt_apply_zero, addCoord, zeroCoord] using
    congrArg (fun A => A.outcome a) h

end DiagonalLine



















/-- The stronger transport-level diagonal compatibility implies the older
outcome-level reparametrization invariant predicate. -/
theorem DiagonalMeasurementTransportInvariant.toEvaluationReparamInvariant
    {params : Parameters} [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : IdxProjMeas (DiagonalLine params) (DiagonalLinePolynomial params) ι}
    (hM : DiagonalMeasurementTransportInvariant params M) :
    DiagonalEvaluationReparamInvariant params M := by
  intro ℓ t a
  rw [hM ℓ t]
  exact DiagonalLine.transportMeasurement_postprocess_zero
    (params := params) (M := M ℓ) t a





namespace AxisParallelCovariantMeasurement



end AxisParallelCovariantMeasurement





namespace DiagonalCovariantMeasurement

/-- A covariant wrapper automatically satisfies the older evaluation-level
rebasing invariant. -/
theorem reparamInvariant {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : DiagonalCovariantMeasurement params ι) :
    DiagonalEvaluationReparamInvariant params M.toIdxProjMeas :=
  M.transportInvariant.toEvaluationReparamInvariant

end DiagonalCovariantMeasurement











-- NOTE: no global `Inhabited` instance for `SymStrat`; constructing default
-- projective measurement families is non-canonical and requires additional
-- assumptions on outcome types.





















-- Paper: `not:conditioned-on-last-direction` abbreviates the axis-parallel
-- line in the last coordinate direction of `F_q^(m+1)` by its base point `u`.


-- Paper: `not:conditioned-on-last-direction` writes `B^u` for the axis-parallel
-- line measurement conditioned on the last direction choice.






namespace AnswerSymStrat

















end AnswerSymStrat



end MIPStarRE.LDT

end

end LIDT

open LIDT
/-!
# Section 10 — commutativity points approximation layer

Restricted-diagonal approximation infrastructure for commutativity at points.
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.CommutativityPoints

open MIPStarRE.LDT.GlobalVariance (PointPairQuestion)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped _root_.Matrix MatrixOrder ComplexOrder BigOperators

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters)
    [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (strategy : _root_.LIDT.MIPStarRE.LDT.SymStrat params ι)
    (eps delta gamma : _root_.LIDT.MIPStarRE.LDT.Error)
    (hgood : strategy.IsGood eps delta gamma) :
    _root_.LIDT.MIPStarRE.LDT.SDDRel strategy.state
      (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointWithDiagonalLineDistribution params)
      (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft
        (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sampledPointMeasurement params strategy))
      (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight
        (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sampledDiagonalLineEvaluation params strategy))
      (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointDiagonalLineApproxError params gamma) := by
  let j := lastRestrictionIndex params
  let e := rebasedLastRestrictedQuestionEquiv params
  rcases sampledDiagonalLineApproximation params strategy eps delta gamma hgood with ⟨hbase⟩
  let f : _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.PointDiagonalLineQuestion params → _root_.LIDT.MIPStarRE.LDT.Error := fun q =>
    _root_.LIDT.MIPStarRE.LDT.qSDD strategy.state
      ((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sampledPointMeasurement params strategy)) q)
      ((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sampledDiagonalLineEvaluation params strategy)) q)
  have hreindex :
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointWithDiagonalLineDistribution params) f =
        _root_.LIDT.MIPStarRE.LDT.avgOver
          (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.RestrictedDiagonalSample params j × _root_.LIDT.MIPStarRE.LDT.Fq params))
          (fun st => f (e st)) := by
    symm
    simpa [_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointWithDiagonalLineDistribution, f] using
      (_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_equiv e (fun st => f (e st)))
  let g : _root_.LIDT.MIPStarRE.LDT.RestrictedDiagonalSample params j → _root_.LIDT.MIPStarRE.LDT.Error := fun s =>
    _root_.LIDT.MIPStarRE.LDT.qSDD strategy.state
      ((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft (_root_.LIDT.MIPStarRE.LDT.diagonalPointAnswerFamily strategy j)) s)
      ((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight (rawDiagonalLineAnswerFamily params strategy j)) s)
  have hignore :
      _root_.LIDT.MIPStarRE.LDT.avgOver
          (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.RestrictedDiagonalSample params j × _root_.LIDT.MIPStarRE.LDT.Fq params))
          (fun st => g st.1) =
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.RestrictedDiagonalSample params j)) g := by
    exact _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_fst g
  refine ⟨?_⟩
  calc
    _root_.LIDT.MIPStarRE.LDT.sddError strategy.state
        (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointWithDiagonalLineDistribution params)
        (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sampledPointMeasurement params strategy))
        (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sampledDiagonalLineEvaluation params strategy))
      = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointWithDiagonalLineDistribution params) f := by
          rfl
    _ = _root_.LIDT.MIPStarRE.LDT.avgOver
          (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.RestrictedDiagonalSample params j × _root_.LIDT.MIPStarRE.LDT.Fq params))
          (fun st => f (e st)) := hreindex
    _ = _root_.LIDT.MIPStarRE.LDT.avgOver
          (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.RestrictedDiagonalSample params j × _root_.LIDT.MIPStarRE.LDT.Fq params))
          (fun st =>
            _root_.LIDT.MIPStarRE.LDT.qSDD strategy.state
              ((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft (_root_.LIDT.MIPStarRE.LDT.diagonalPointAnswerFamily strategy j)) st.1)
              ((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight (rawDiagonalLineAnswerFamily params strategy j)) st.1)) := by
            apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
            rintro ⟨s, t⟩
            let ℓ₀ : _root_.LIDT.MIPStarRE.LDT.DiagonalLine params := lastRestrictedSampleEquivDiagonalLine params s
            have hpoint : _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sampledPointFromDiagonalQuestion params (e (s, t)) = s.1 := by
              change (_root_.LIDT.MIPStarRE.LDT.DiagonalLine.rebaseAt ℓ₀ (_root_.LIDT.MIPStarRE.LDT.subCoord _root_.LIDT.MIPStarRE.LDT.zeroCoord t)).pointAt t = s.1
              calc
                (_root_.LIDT.MIPStarRE.LDT.DiagonalLine.rebaseAt ℓ₀ (_root_.LIDT.MIPStarRE.LDT.subCoord _root_.LIDT.MIPStarRE.LDT.zeroCoord t)).pointAt t
                  = ℓ₀.pointAt (_root_.LIDT.MIPStarRE.LDT.addCoord (_root_.LIDT.MIPStarRE.LDT.subCoord _root_.LIDT.MIPStarRE.LDT.zeroCoord t) t) := by
                      simpa using _root_.LIDT.MIPStarRE.LDT.DiagonalLine.rebaseAt_pointAt ℓ₀ (_root_.LIDT.MIPStarRE.LDT.subCoord _root_.LIDT.MIPStarRE.LDT.zeroCoord t) t
                _ = ℓ₀.pointAt _root_.LIDT.MIPStarRE.LDT.zeroCoord := by simp
                _ = s.1 := by
                      rcases s with ⟨u, free⟩
                      funext i
                      simp [ℓ₀, lastRestrictedSampleEquivDiagonalLine, _root_.LIDT.MIPStarRE.LDT.DiagonalLine.pointAt,
                        _root_.LIDT.MIPStarRE.LDT.addPoint, _root_.LIDT.MIPStarRE.LDT.smulPoint, _root_.LIDT.MIPStarRE.LDT.zeroCoord, _root_.LIDT.MIPStarRE.LDT.addCoord, _root_.LIDT.MIPStarRE.LDT.mulCoord]
            have hA : ∀ a,
                (((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft
                    (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sampledPointMeasurement params strategy)) (e (s, t))).outcome a) =
                  (((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft (_root_.LIDT.MIPStarRE.LDT.diagonalPointAnswerFamily strategy j)) s).outcome a) := by
              intro a
              simp [_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft, _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sampledPointMeasurement, _root_.LIDT.MIPStarRE.LDT.diagonalPointAnswerFamily,
                _root_.LIDT.MIPStarRE.LDT.diagonalPointAnswerFamilyOf, hpoint]
            have hB : ∀ a,
                (((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sampledDiagonalLineEvaluation params strategy))
                    (e (s, t))).outcome a) =
                  (((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight
                      (rawDiagonalLineAnswerFamily params strategy j)) s).outcome a) := by
              intro a
              have hreparam :=
                (_root_.LIDT.MIPStarRE.LDT.DiagonalCovariantMeasurement.reparamInvariant
                  strategy.diagonalMeasurement)
                  (_root_.LIDT.MIPStarRE.LDT.DiagonalLine.rebaseAt ℓ₀ (_root_.LIDT.MIPStarRE.LDT.subCoord _root_.LIDT.MIPStarRE.LDT.zeroCoord t)) t a
              have hline :
                  ((_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sampledDiagonalLineEvaluation params strategy) (e (s, t))).outcome a =
                    (rawDiagonalLineAnswerFamily params strategy j s).outcome a := by
                calc
                  ((_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sampledDiagonalLineEvaluation params strategy) (e (s, t))).outcome a
                    = (_root_.LIDT.MIPStarRE.LDT.postprocess
                        ((strategy.diagonalMeasurement
                          (_root_.LIDT.MIPStarRE.LDT.DiagonalLine.rebaseAt ℓ₀ (_root_.LIDT.MIPStarRE.LDT.subCoord _root_.LIDT.MIPStarRE.LDT.zeroCoord t))).toSubMeas)
                        (fun f => f t)).outcome a := by
                            simp [_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sampledDiagonalLineEvaluation, e,
                              rebasedLastRestrictedQuestionEquiv, ℓ₀]
                  _ = (_root_.LIDT.MIPStarRE.LDT.postprocess
                        ((strategy.diagonalMeasurement
                          (_root_.LIDT.MIPStarRE.LDT.DiagonalLine.rebaseAt
                            (_root_.LIDT.MIPStarRE.LDT.DiagonalLine.rebaseAt ℓ₀ (_root_.LIDT.MIPStarRE.LDT.subCoord _root_.LIDT.MIPStarRE.LDT.zeroCoord t)) t)).toSubMeas)
                        (fun f => f _root_.LIDT.MIPStarRE.LDT.zeroCoord)).outcome a := by
                            symm
                            exact hreparam
                  _ = (_root_.LIDT.MIPStarRE.LDT.postprocess
                        ((strategy.diagonalMeasurement ℓ₀).toSubMeas)
                        (fun f => f _root_.LIDT.MIPStarRE.LDT.zeroCoord)).outcome a := by
                            simp [_root_.LIDT.MIPStarRE.LDT.DiagonalLine.rebaseAt_rebase, _root_.LIDT.MIPStarRE.LDT.addCoord_subCoord_left]
                  _ = (rawDiagonalLineAnswerFamily params strategy j s).outcome a := by
                            rcases s with ⟨u, free⟩
                            change
                              (_root_.LIDT.MIPStarRE.LDT.postprocess
                                ((strategy.diagonalMeasurement
                                  { base := u,
                                    direction :=
                                      lastRestrictedDirectionEquiv params free
                                  }).toSubMeas)
                                (fun f => f _root_.LIDT.MIPStarRE.LDT.zeroCoord)).outcome a =
                              (_root_.LIDT.MIPStarRE.LDT.postprocess
                                ((strategy.diagonalMeasurement
                                  { base := u,
                                    direction :=
                                      _root_.LIDT.MIPStarRE.LDT.extendRestrictedDirection
                                        (lastRestrictionIndex params) free
                                  }).toSubMeas)
                                (fun f => f _root_.LIDT.MIPStarRE.LDT.zeroCoord)).outcome a
                            simp [lastRestrictedDirectionEquiv]
              simpa [_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight] using
                congrArg (fun X => _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) X) hline
            unfold f _root_.LIDT.MIPStarRE.LDT.qSDD _root_.LIDT.MIPStarRE.LDT.qSDDCore
            apply Finset.sum_congr rfl
            intro a _
            rw [hA a, hB a]
    _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.RestrictedDiagonalSample params j))
          g := hignore
    _ = _root_.LIDT.MIPStarRE.LDT.sddError strategy.state
          (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.RestrictedDiagonalSample params j))
          (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft (_root_.LIDT.MIPStarRE.LDT.diagonalPointAnswerFamily strategy j))
          (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight (rawDiagonalLineAnswerFamily params strategy j)) := by
            rfl
    _ ≤ _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointDiagonalLineApproxError params gamma := hbase
