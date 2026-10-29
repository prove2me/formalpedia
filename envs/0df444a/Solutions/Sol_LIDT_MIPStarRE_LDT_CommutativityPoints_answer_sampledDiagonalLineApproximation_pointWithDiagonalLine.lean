-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.CommutativityPoints.answer_sampledDiagonalLineApproximation_pointWithDiagonalLine
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T14:08:57.861165+00:00
-- url     : https://prove2.me/submissions/32550560-48b5-4713-9bf5-8b6390e4f498

-- Generated proof for MIPStarRE.LDT.CommutativityPoints.answer_sampledDiagonalLineApproximation_pointWithDiagonalLine.
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































/-- The answer-valued diagonal-line test controls the final restricted
diagonal slice. -/
private lemma answer_sampledDiagonalLineConsistency
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    ConsRel strategy.state
      (uniformDistribution (RestrictedDiagonalSample params (lastRestrictionIndex params)))
      (AnswerSymStrat.diagonalPointAnswerFamily strategy (lastRestrictionIndex params))
      (rawAnswerDiagonalLineAnswerFamily params strategy (lastRestrictionIndex params))
      (restrictedDiagonalLinesConsistencyError params gamma) := by
  let j := lastRestrictionIndex params
  let err : Fin params.m → Error := fun j =>
    bipartiteConsError strategy.state
      (uniformDistribution (RestrictedDiagonalSample params j))
      (AnswerSymStrat.diagonalPointAnswerFamily strategy j)
      (rawAnswerDiagonalLineAnswerFamily params strategy j)
  have herr_nonneg : ∀ j : Fin params.m, 0 ≤ err j := by
    intro j'
    exact bipartiteConsError_nonneg strategy.state
      (uniformDistribution (RestrictedDiagonalSample params j'))
      (AnswerSymStrat.diagonalPointAnswerFamily strategy j')
      (rawAnswerDiagonalLineAnswerFamily params strategy j')
  have hsum_bound : ∑ j' : Fin params.m, err j' ≤ gamma * (params.m : Error) := by
    have hm_nonneg : 0 ≤ (params.m : Error) := by
      positivity
    have hm_ne : (params.m : Error) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt params.hm
    have hdiag := hgood.diagonalLineTest
    dsimp [AnswerSymStrat.diagonalFailureProbability, err,
      AnswerSymStrat.diagonalLineAnswerFamily, rawAnswerDiagonalLineAnswerFamily] at hdiag
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

/-- The answer-valued restricted diagonal test gives the same SDD
approximation at the final restriction index as the ordinary diagonal test. -/
private lemma answer_sampledDiagonalLineApproximation
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    SDDRel strategy.state
      (uniformDistribution (RestrictedDiagonalSample params (lastRestrictionIndex params)))
      (IdxSubMeas.liftLeft
        (AnswerSymStrat.diagonalPointAnswerFamily strategy (lastRestrictionIndex params)))
      (IdxSubMeas.liftRight
        (rawAnswerDiagonalLineAnswerFamily params strategy (lastRestrictionIndex params)))
      (pointDiagonalLineApproxError params gamma) := by
  let j := lastRestrictionIndex params
  let pointFamily : IdxMeas (RestrictedDiagonalSample params j) (Fq params) ι :=
    fun s => (strategy.pointMeasurement s.1).toMeasurement
  let lineFamily : IdxMeas (RestrictedDiagonalSample params j) (Fq params) ι :=
    fun s =>
      { toSubMeas := rawAnswerDiagonalLineAnswerFamily params strategy j s
        total_eq_one :=
          calc
            (rawAnswerDiagonalLineAnswerFamily params strategy j s).total =
                ((strategy.diagonalMeasurement
                  { base := s.1
                    direction := extendRestrictedDirection j s.2 }).toSubMeas).total := by
              dsimp [rawAnswerDiagonalLineAnswerFamily]
              rw [postprocess_total]
            _ = 1 :=
              (strategy.diagonalMeasurement
                { base := s.1
                  direction := extendRestrictedDirection j s.2 }).total_eq_one }
  have hcons := answer_sampledDiagonalLineConsistency params strategy eps delta gamma hgood
  have hcons' :
      ConsRel strategy.state
        (uniformDistribution (RestrictedDiagonalSample params j))
        (IdxMeas.toIdxSubMeas pointFamily)
        (IdxMeas.toIdxSubMeas lineFamily)
        (restrictedDiagonalLinesConsistencyError params gamma) := by
    change ConsRel strategy.state
      (uniformDistribution (RestrictedDiagonalSample params (lastRestrictionIndex params)))
      (diagonalPointAnswerFamilyOf strategy.pointMeasurement (lastRestrictionIndex params))
      (rawAnswerDiagonalLineAnswerFamily params strategy (lastRestrictionIndex params))
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
  simpa [j, pointFamily, lineFamily, AnswerSymStrat.diagonalPointAnswerFamily,
    pointDiagonalLineApproxError, restrictedDiagonalLinesConsistencyError,
    Preliminaries.BipartiteSDDRel, sddError, IdxMeas.toIdxSubMeas,
    IdxSubMeas.liftLeft, IdxSubMeas.liftRight] using
    happrox.leftRightSquaredDistanceBound



end MIPStarRE.LDT.CommutativityPoints

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
    (strategy : _root_.LIDT.MIPStarRE.LDT.AnswerSymStrat params ι)
    (eps delta gamma : _root_.LIDT.MIPStarRE.LDT.Error)
    (hgood : strategy.IsGood eps delta gamma) :
    _root_.LIDT.MIPStarRE.LDT.SDDRel strategy.state
      (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointWithDiagonalLineDistribution params)
      (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft
        (fun q =>
          (strategy.pointMeasurement (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sampledPointFromDiagonalQuestion params q)).toSubMeas))
      (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight
        (fun q =>
          _root_.LIDT.MIPStarRE.LDT.postprocess ((strategy.diagonalMeasurement q.1).toSubMeas) (fun f => f q.2)))
      (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointDiagonalLineApproxError params gamma) := by
  let j := lastRestrictionIndex params
  let e := rebasedLastRestrictedQuestionEquiv params
  rcases answer_sampledDiagonalLineApproximation params strategy eps delta gamma hgood with
    ⟨hbase⟩
  let f : _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.PointDiagonalLineQuestion params → _root_.LIDT.MIPStarRE.LDT.Error := fun q =>
    _root_.LIDT.MIPStarRE.LDT.qSDD strategy.state
      ((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft
        (fun q =>
          (strategy.pointMeasurement (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sampledPointFromDiagonalQuestion params q)).toSubMeas)) q)
      ((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight
        (fun q => _root_.LIDT.MIPStarRE.LDT.postprocess ((strategy.diagonalMeasurement q.1).toSubMeas)
          (fun f => f q.2))) q)
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
      ((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft (_root_.LIDT.MIPStarRE.LDT.AnswerSymStrat.diagonalPointAnswerFamily strategy j)) s)
      ((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight (rawAnswerDiagonalLineAnswerFamily params strategy j)) s)
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
        (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft
          (fun q =>
            (strategy.pointMeasurement (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sampledPointFromDiagonalQuestion params q)).toSubMeas))
        (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight
          (fun q => _root_.LIDT.MIPStarRE.LDT.postprocess ((strategy.diagonalMeasurement q.1).toSubMeas)
            (fun f => f q.2)))
      = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointWithDiagonalLineDistribution params) f := by
          rfl
    _ = _root_.LIDT.MIPStarRE.LDT.avgOver
          (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.RestrictedDiagonalSample params j × _root_.LIDT.MIPStarRE.LDT.Fq params))
          (fun st => f (e st)) := hreindex
    _ = _root_.LIDT.MIPStarRE.LDT.avgOver
          (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.RestrictedDiagonalSample params j × _root_.LIDT.MIPStarRE.LDT.Fq params))
          (fun st =>
            _root_.LIDT.MIPStarRE.LDT.qSDD strategy.state
              ((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft
                (_root_.LIDT.MIPStarRE.LDT.AnswerSymStrat.diagonalPointAnswerFamily strategy j)) st.1)
              ((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight
                  (rawAnswerDiagonalLineAnswerFamily params strategy j)) st.1)) := by
            apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
            rintro ⟨s, t⟩
            let ℓ₀ : _root_.LIDT.MIPStarRE.LDT.DiagonalLine params := lastRestrictedSampleEquivDiagonalLine params s
            have hpoint : _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sampledPointFromDiagonalQuestion params (e (s, t)) = s.1 := by
              change (_root_.LIDT.MIPStarRE.LDT.DiagonalLine.rebaseAt ℓ₀ (_root_.LIDT.MIPStarRE.LDT.subCoord _root_.LIDT.MIPStarRE.LDT.zeroCoord t)).pointAt t = s.1
              calc
                (_root_.LIDT.MIPStarRE.LDT.DiagonalLine.rebaseAt ℓ₀ (_root_.LIDT.MIPStarRE.LDT.subCoord _root_.LIDT.MIPStarRE.LDT.zeroCoord t)).pointAt t
                  = ℓ₀.pointAt (_root_.LIDT.MIPStarRE.LDT.addCoord (_root_.LIDT.MIPStarRE.LDT.subCoord _root_.LIDT.MIPStarRE.LDT.zeroCoord t) t) := by
                      simpa using
                        _root_.LIDT.MIPStarRE.LDT.DiagonalLine.rebaseAt_pointAt ℓ₀ (_root_.LIDT.MIPStarRE.LDT.subCoord _root_.LIDT.MIPStarRE.LDT.zeroCoord t) t
                _ = ℓ₀.pointAt _root_.LIDT.MIPStarRE.LDT.zeroCoord := by simp
                _ = s.1 := by
                      rcases s with ⟨u, free⟩
                      funext i
                      simp [ℓ₀, lastRestrictedSampleEquivDiagonalLine, _root_.LIDT.MIPStarRE.LDT.DiagonalLine.pointAt,
                        _root_.LIDT.MIPStarRE.LDT.addPoint, _root_.LIDT.MIPStarRE.LDT.smulPoint, _root_.LIDT.MIPStarRE.LDT.zeroCoord, _root_.LIDT.MIPStarRE.LDT.addCoord, _root_.LIDT.MIPStarRE.LDT.mulCoord]
            have hA : ∀ a,
                (((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft
                    (fun q => (strategy.pointMeasurement
                      (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sampledPointFromDiagonalQuestion params q)).toSubMeas))
                      (e (s, t))).outcome a) =
                  (((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft
                    (_root_.LIDT.MIPStarRE.LDT.AnswerSymStrat.diagonalPointAnswerFamily strategy j)) s).outcome a) := by
              intro a
              simp [_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft, _root_.LIDT.MIPStarRE.LDT.AnswerSymStrat.diagonalPointAnswerFamily,
                _root_.LIDT.MIPStarRE.LDT.diagonalPointAnswerFamilyOf, hpoint]
            have hB : ∀ a,
                (((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight
                    (fun q => _root_.LIDT.MIPStarRE.LDT.postprocess ((strategy.diagonalMeasurement q.1).toSubMeas)
                      (fun f => f q.2))) (e (s, t))).outcome a) =
                  (((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight
                      (rawAnswerDiagonalLineAnswerFamily params strategy j)) s).outcome a) := by
              intro a
              have hline :
                  (_root_.LIDT.MIPStarRE.LDT.postprocess
                    ((strategy.diagonalMeasurement (e (s, t)).1).toSubMeas)
                    (fun f => f (e (s, t)).2)).outcome a =
                    (rawAnswerDiagonalLineAnswerFamily params strategy j s).outcome a := by
                have htransport :=
                  strategy.diagonalMeasurement.transportInvariant
                    (_root_.LIDT.MIPStarRE.LDT.DiagonalLine.rebaseAt ℓ₀ (_root_.LIDT.MIPStarRE.LDT.subCoord _root_.LIDT.MIPStarRE.LDT.zeroCoord t)) t
                have hpost :
                    _root_.LIDT.MIPStarRE.LDT.postprocess
                        ((_root_.LIDT.MIPStarRE.LDT.ProjMeas.transport
                          (_root_.LIDT.MIPStarRE.LDT.DiagonalLineAnswer.reparamAtEquiv (params := params) t)
                          (strategy.diagonalMeasurement
                            (_root_.LIDT.MIPStarRE.LDT.DiagonalLine.rebaseAt ℓ₀ (_root_.LIDT.MIPStarRE.LDT.subCoord _root_.LIDT.MIPStarRE.LDT.zeroCoord t)))).toSubMeas)
                        (fun f : _root_.LIDT.MIPStarRE.LDT.DiagonalLineAnswer params => f t) =
                      _root_.LIDT.MIPStarRE.LDT.postprocess
                        ((strategy.diagonalMeasurement
                          (_root_.LIDT.MIPStarRE.LDT.DiagonalLine.rebaseAt ℓ₀ (_root_.LIDT.MIPStarRE.LDT.subCoord _root_.LIDT.MIPStarRE.LDT.zeroCoord t))).toSubMeas)
                        (fun f : _root_.LIDT.MIPStarRE.LDT.DiagonalLineAnswer params => f (_root_.LIDT.MIPStarRE.LDT.addCoord t t)) := by
                  simpa [_root_.LIDT.MIPStarRE.LDT.ProjMeas.transport, _root_.LIDT.MIPStarRE.LDT.Measurement.transport, _root_.LIDT.MIPStarRE.LDT.SubMeas.transport,
                    _root_.LIDT.MIPStarRE.LDT.DiagonalLineAnswer.reparamAtEquiv] using
                    (_root_.LIDT.MIPStarRE.LDT.SubMeas.postprocess_transport
                      (e := _root_.LIDT.MIPStarRE.LDT.DiagonalLineAnswer.reparamAtEquiv (params := params) t)
                      (A := (strategy.diagonalMeasurement
                        (_root_.LIDT.MIPStarRE.LDT.DiagonalLine.rebaseAt ℓ₀ (_root_.LIDT.MIPStarRE.LDT.subCoord _root_.LIDT.MIPStarRE.LDT.zeroCoord t))).toSubMeas)
                      (f := fun f : _root_.LIDT.MIPStarRE.LDT.DiagonalLineAnswer params => f t))
                calc
                  (_root_.LIDT.MIPStarRE.LDT.postprocess
                    ((strategy.diagonalMeasurement (e (s, t)).1).toSubMeas)
                    (fun f => f (e (s, t)).2)).outcome a
                    = (_root_.LIDT.MIPStarRE.LDT.postprocess
                        ((strategy.diagonalMeasurement
                          (_root_.LIDT.MIPStarRE.LDT.DiagonalLine.rebaseAt ℓ₀ (_root_.LIDT.MIPStarRE.LDT.subCoord _root_.LIDT.MIPStarRE.LDT.zeroCoord t))).toSubMeas)
                        (fun f : _root_.LIDT.MIPStarRE.LDT.DiagonalLineAnswer params => f t)).outcome a := by
                          simp [e, rebasedLastRestrictedQuestionEquiv, ℓ₀]
                  _ = (_root_.LIDT.MIPStarRE.LDT.postprocess
                        ((_root_.LIDT.MIPStarRE.LDT.ProjMeas.transport
                          (_root_.LIDT.MIPStarRE.LDT.DiagonalLineAnswer.reparamAtEquiv (params := params)
                            (_root_.LIDT.MIPStarRE.LDT.subCoord _root_.LIDT.MIPStarRE.LDT.zeroCoord t))
                          (strategy.diagonalMeasurement ℓ₀)).toSubMeas)
                        (fun f : _root_.LIDT.MIPStarRE.LDT.DiagonalLineAnswer params => f t)).outcome a := by
                          rw [strategy.diagonalMeasurement.transportInvariant ℓ₀
                            (_root_.LIDT.MIPStarRE.LDT.subCoord _root_.LIDT.MIPStarRE.LDT.zeroCoord t)]
                  _ = (_root_.LIDT.MIPStarRE.LDT.postprocess
                        ((strategy.diagonalMeasurement ℓ₀).toSubMeas)
                        (fun f : _root_.LIDT.MIPStarRE.LDT.DiagonalLineAnswer params =>
                          f (_root_.LIDT.MIPStarRE.LDT.addCoord (_root_.LIDT.MIPStarRE.LDT.subCoord _root_.LIDT.MIPStarRE.LDT.zeroCoord t) t))).outcome a := by
                          have h :=
                            _root_.LIDT.MIPStarRE.LDT.SubMeas.postprocess_transport
                              (e := _root_.LIDT.MIPStarRE.LDT.DiagonalLineAnswer.reparamAtEquiv (params := params)
                                (_root_.LIDT.MIPStarRE.LDT.subCoord _root_.LIDT.MIPStarRE.LDT.zeroCoord t))
                              (A := (strategy.diagonalMeasurement ℓ₀).toSubMeas)
                              (f := fun f : _root_.LIDT.MIPStarRE.LDT.DiagonalLineAnswer params => f t)
                          simpa [_root_.LIDT.MIPStarRE.LDT.ProjMeas.transport, _root_.LIDT.MIPStarRE.LDT.Measurement.transport,
                            _root_.LIDT.MIPStarRE.LDT.DiagonalLineAnswer.reparamAtEquiv,
                            _root_.LIDT.MIPStarRE.LDT.DiagonalLineAnswer.reparamAt] using
                            congrArg (fun M : _root_.LIDT.MIPStarRE.LDT.SubMeas (_root_.LIDT.MIPStarRE.LDT.Fq params) ι => M.outcome a) h
                  _ = (_root_.LIDT.MIPStarRE.LDT.postprocess
                        ((strategy.diagonalMeasurement ℓ₀).toSubMeas)
                        (fun f : _root_.LIDT.MIPStarRE.LDT.DiagonalLineAnswer params => f _root_.LIDT.MIPStarRE.LDT.zeroCoord)).outcome a := by
                          simp
                  _ = (rawAnswerDiagonalLineAnswerFamily params strategy j s).outcome a := by
                          rcases s with ⟨u, free⟩
                          change
                            (_root_.LIDT.MIPStarRE.LDT.postprocess
                              ((strategy.diagonalMeasurement
                                { base := u,
                                  direction :=
                                    lastRestrictedDirectionEquiv params free
                                }).toSubMeas)
                              (fun f : _root_.LIDT.MIPStarRE.LDT.DiagonalLineAnswer params => f _root_.LIDT.MIPStarRE.LDT.zeroCoord)).outcome a =
                            (_root_.LIDT.MIPStarRE.LDT.postprocess
                              ((strategy.diagonalMeasurement
                                { base := u,
                                  direction :=
                                    _root_.LIDT.MIPStarRE.LDT.extendRestrictedDirection
                                      (lastRestrictionIndex params) free
                                }).toSubMeas)
                              (fun f : _root_.LIDT.MIPStarRE.LDT.DiagonalLineAnswer params => f _root_.LIDT.MIPStarRE.LDT.zeroCoord)).outcome a
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
          (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft (_root_.LIDT.MIPStarRE.LDT.AnswerSymStrat.diagonalPointAnswerFamily strategy j))
          (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight (rawAnswerDiagonalLineAnswerFamily params strategy j)) := by
            rfl
    _ ≤ _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointDiagonalLineApproxError params gamma := hbase
