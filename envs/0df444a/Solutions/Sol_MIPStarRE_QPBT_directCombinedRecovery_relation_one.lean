-- Prove2me | solution 1 for MIPStarRE.QPBT.directCombinedRecovery_relation_one
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:58:14.655264+00:00
-- url     : https://prove2.me/submissions/7be6b22b-27a8-4d0c-b918-522ef3f287b8

-- Generated proof for MIPStarRE.QPBT.directCombinedRecovery_relation_one.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Parameters
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Polynomial
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Recovery
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_RecoveryTransport
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Strategy
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGameMeasurements
import Mathlib
import Theorems.Thm_LIDT_MIPStarRE_Quantum_Measurement_postprocess_comp
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_congr
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_le_of_recoveryBound
import Theorems.Thm_MIPStarRE_QPBT_directCombinedRecoveryEvent_avg_le
import Theorems.Thm_MIPStarRE_QPBT_directCombinedRecoveryLocalBound_avg_le

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus

/- Source helpers from QPBT/Combining/DirectLowDegree/Transport/Combining/RecoveryTransport.lean. -/
/-!
# The recovery of the polynomial-tuple measurements

`lem:ld-combining-recovery` turns the three conclusions of `lem:ld-soundness`
for the combined strategy at the combined parameters into the three conclusions
for the original strategy at the original parameters, by post-processing the
measurements of the combined game with the recovery map of
`def:ld-combining-map`.

The two point relations follow from the consistency-defect transport
inequality.  At a point `(u, α)` of the combined space the point measurement of
the combined strategy is the point measurement of the original strategy at `u`
post-processed by the combination with coefficients `α`, and the polynomial
measurement of the combined game read at that point is the same measurement
read through the recovery map and then combined with the same coefficients; the
two families therefore differ only on the recovery discrepancy event, whose
average is `(m + k) d / q`.  The uniform law on the combined space is the
product of the uniform laws on the point part and on the combining part, which
is the reindexing along
`directCombinedPointEquiv`.

The polynomial relation is data processing: the recovered measurements are
post-processings of the measurements of the combined game.

## Main statements

* `directCombinedPointEquiv` — the point of the combined space with given
  point and combining parts, as an identification.
* `directCombinedRecovery_relation_one` — the first conclusion.
* `directCombinedRecovery_relation_two` — the second conclusion.
* `directCombinedRecovery_relation_three` — the third conclusion.

## References

* `references/neexp-paper/05_quantum_preliminaries.tex:1440-1503`
* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:617-680`
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.LDT.Preliminaries
open LIDT.MIPStarRE.Quantum
open DistanceCalculus

noncomputable section

/-! ## The two blocks of a point of the combined space -/





/-! ## The point measurement of the combined strategy -/

/-- On a point question of the combined game the combined strategy measures the
point question of the original game at the point part. -/
private theorem directCombinedMeasuredQuestion_point (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (u : Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) (α : Fin D.k → _root_.MIPStarRE.QPBT.DirectScalarQ D) :
    _root_.MIPStarRE.QPBT.directCombinedMeasuredQuestion D
        (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D.combined (_root_.MIPStarRE.QPBT.combinedPoint u α)) =
      _root_.MIPStarRE.QPBT.directLdPointQuestionOf D u := by
  show _root_.MIPStarRE.QPBT.directLdPointQuestionOf D
    (_root_.MIPStarRE.QPBT.directCombinedPointPart D (_root_.MIPStarRE.QPBT.combinedPoint u α)) = _
  rw [_root_.MIPStarRE.QPBT.directCombinedPointPart_combinedPoint]

/-- On a point question of the combined game the combined answer, read as a
one-component tuple of scalars, is the combination of the measured point answer
with the combining part of the sampled point. -/
private theorem directCombinedPointAnswerMap_comp (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (u : Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) (α : Fin D.k → _root_.MIPStarRE.QPBT.DirectScalarQ D) :
    (fun a : _root_.MIPStarRE.QPBT.DirectLdAnswer D => _root_.MIPStarRE.QPBT.directLdPointValuesOrZero D.combined
        (_root_.MIPStarRE.QPBT.directCombinedAnswerMap D
          (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D.combined (_root_.MIPStarRE.QPBT.combinedPoint u α)) a)) =
      fun a : _root_.MIPStarRE.QPBT.DirectLdAnswer D => (fun _ : Fin D.combined.k =>
        ∑ r : Fin D.k, α r * _root_.MIPStarRE.QPBT.directLdPointValuesOrZero D a r) := by
  funext a
  cases a with
  | pointVals b =>
      funext j
      show (∑ r : Fin D.k,
        _root_.MIPStarRE.QPBT.directCombinedCoefficientPart D (_root_.MIPStarRE.QPBT.combinedPoint u α) r * b r) = _
      rw [_root_.MIPStarRE.QPBT.directCombinedCoefficientPart_combinedPoint]
      rfl
  | alinePolys g =>
      funext j
      show (0 : _root_.MIPStarRE.QPBT.DirectScalarQ D) =
        ∑ r : Fin D.k, α r * (0 : Fin D.k → _root_.MIPStarRE.QPBT.DirectScalarQ D) r
      simp
  | dlinePolys g =>
      funext j
      show (0 : _root_.MIPStarRE.QPBT.DirectScalarQ D) =
        ∑ r : Fin D.k, α r * (0 : Fin D.k → _root_.MIPStarRE.QPBT.DirectScalarQ D) r
      simp

/-! ## The discrepancy estimate in the shape of the transport -/

/-- A constant function on a one-element index set equals a function exactly
when the value of the function at the unique index is the constant. -/
private theorem const_eq_fun_iff {ι K : Type*} [Unique ι] (c : K) (h : ι → K) :
    ((fun _ : ι => c) = h) ↔ h default = c := by
  constructor
  · intro hh
    rw [← hh]
  · intro hh
    funext i
    rw [Unique.eq_default i, hh]

set_option maxHeartbeats 1600000 in
/-- The discrepancy estimate of `Recovery` in the shape required by the
transport: for a fixed point, a fixed point answer and a fixed outcome of the
combined game, the probability over the combining vector that the recovered
tuple of values differs from the point answer while the outcome read at the
combined point agrees with the combination is at most the local bound. -/
private theorem directCombinedRecoveryEvent_transport (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (u : Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) (b : Fin D.k → _root_.MIPStarRE.QPBT.DirectScalarQ D)
    (p : _root_.MIPStarRE.QPBT.DirectPolyTuple D.combined) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.k → _root_.MIPStarRE.QPBT.DirectScalarQ D)) (fun α =>
        if _root_.MIPStarRE.QPBT.evalDirectPolyTupleAt u (_root_.MIPStarRE.QPBT.directTupleOfCombinedTuple D p) ≠ b ∧
            (fun _ : Fin D.combined.k => ∑ r : Fin D.k, α r * b r) =
              _root_.MIPStarRE.QPBT.evalDirectPolyTupleAt (D := D.combined) (_root_.MIPStarRE.QPBT.combinedPoint u α) p then
          (1 : ℝ) else 0) ≤
      _root_.MIPStarRE.QPBT.directCombinedRecoveryLocalBound D (p default) u := by
  classical
  refine le_trans (le_of_eq (_root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ fun α => ?_))
    (_root_.MIPStarRE.QPBT.directCombinedRecoveryEvent_avg_le D (p default) u b)
  exact if_congr (and_congr Iff.rfl (const_eq_fun_iff _
    (_root_.MIPStarRE.QPBT.evalDirectPolyTupleAt (D := D.combined) (_root_.MIPStarRE.QPBT.combinedPoint u α) p))) rfl rfl

/-! ## The two point relations -/





/-! ## The polynomial relation -/



end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Games/Consistency.lean. -/
/-! # State-dependent consistency and strategy closeness

The definitions are the finite-dimensional forms of blueprint
`def:consistency` and `def:strategy-distance`,
from `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:219-288`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum



/-- A uniform consistency defect is invariant under a bijective relabeling of
its question type. -/
theorem consistencyDefect_uniform_question_equiv
    {X Y Outcome iota : Type*}
    [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    [Fintype Outcome] [DecidableEq Outcome]
    [Fintype iota] [DecidableEq iota]
    (e : X ≃ Y) (A B : Y → Outcome → _root_.LIDT.MIPStarRE.Quantum.Op iota)
    (psi : EuclideanSpace ℂ iota) :
    _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution X)
        (fun x a => A (e x) a) (fun x a => B (e x) a) psi =
      _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Y) A B psi := by
  unfold _root_.MIPStarRE.QPBT.consistencyDefect
  simpa using _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_equiv e (fun x =>
    ∑ a : Outcome, ∑ b : Outcome,
      if a = b then 0 else
        (inner ℂ psi ((EuclideanSpace.equiv iota ℂ).symm
          (((A (e x) a) * (B (e x) b)).mulVec psi))).re)















end MIPStarRE.QPBT

/-!
# The recovery of the polynomial-tuple measurements

`lem:ld-combining-recovery` turns the three conclusions of `lem:ld-soundness`
for the combined strategy at the combined parameters into the three conclusions
for the original strategy at the original parameters, by post-processing the
measurements of the combined game with the recovery map of
`def:ld-combining-map`.

The two point relations follow from the consistency-defect transport
inequality.  At a point `(u, α)` of the combined space the point measurement of
the combined strategy is the point measurement of the original strategy at `u`
post-processed by the combination with coefficients `α`, and the polynomial
measurement of the combined game read at that point is the same measurement
read through the recovery map and then combined with the same coefficients; the
two families therefore differ only on the recovery discrepancy event, whose
average is `(m + k) d / q`.  The uniform law on the combined space is the
product of the uniform laws on the point part and on the combining part, which
is the reindexing along
`directCombinedPointEquiv`.

The polynomial relation is data processing: the recovered measurements are
post-processings of the measurements of the combined game.

## Main statements

* `directCombinedPointEquiv` — the point of the combined space with given
  point and combining parts, as an identification.
* `directCombinedRecovery_relation_one` — the first conclusion.
* `directCombinedRecovery_relation_two` — the second conclusion.
* `directCombinedRecovery_relation_three` — the third conclusion.

## References

* `references/neexp-paper/05_quantum_preliminaries.tex:1440-1503`
* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:617-680`
-/



open scoped BigOperators MatrixOrder Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.LDT.Preliminaries
open LIDT.MIPStarRE.Quantum
open MIPStarRE.QPBT.DistanceCalculus



/-! ## The two blocks of a point of the combined space -/





/-! ## The point measurement of the combined strategy -/





/-! ## The discrepancy estimate in the shape of the transport -/





/-! ## The two point relations -/

set_option maxHeartbeats 1600000 in

theorem solution (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.directLdGame D))
    (GB : _root_.MIPStarRE.QPBT.DirectPolyMeasTuple D.combined S.ιB) :
    _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
        (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron
          (((S.A (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)).postprocess
            (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero D)).effect outcome) 1)
        (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron 1
          (((GB.postprocess (_root_.MIPStarRE.QPBT.directTupleOfCombinedTuple D)).postprocess
            (_root_.MIPStarRE.QPBT.evalDirectPolyTupleAt u)).effect outcome))
        S.ψ ≤
      _root_.MIPStarRE.QPBT.consistencyDefect
          (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.combined.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
          (fun z outcome => _root_.MIPStarRE.QPBT.heteroKron
            ((((_root_.MIPStarRE.QPBT.directCombinedStrategy D S).A
              (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D.combined z)).postprocess
                (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero D.combined)).effect outcome) 1)
          (fun z outcome => _root_.MIPStarRE.QPBT.heteroKron 1
            ((GB.postprocess (_root_.MIPStarRE.QPBT.evalDirectPolyTupleAt (D := D.combined) z)).effect
              outcome))
          S.ψ +
        ((D.combined.m * D.d : ℕ) : ℝ) / D.q := by
  classical
  have hkey := _root_.MIPStarRE.QPBT.consistencyDefect_le_of_recoveryBound
    (X := Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) (Y := Fin D.k → _root_.MIPStarRE.QPBT.DirectScalarQ D)
    (fun u => (S.A (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)).postprocess
      (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero D))
    GB S.ψ S.ψ_norm
    (fun u p => _root_.MIPStarRE.QPBT.evalDirectPolyTupleAt u (_root_.MIPStarRE.QPBT.directTupleOfCombinedTuple D p))
    (fun _ α b => (fun _ : Fin D.combined.k => ∑ r : Fin D.k, α r * b r))
    (fun u α p => _root_.MIPStarRE.QPBT.evalDirectPolyTupleAt (D := D.combined) (_root_.MIPStarRE.QPBT.combinedPoint u α) p)
    (fun u p => _root_.MIPStarRE.QPBT.directCombinedRecoveryLocalBound D (p default) u)
    (((D.combined.m * D.d : ℕ) : ℝ) / D.q)
    (fun u b p => directCombinedRecoveryEvent_transport D u b p)
    (fun p => _root_.MIPStarRE.QPBT.directCombinedRecoveryLocalBound_avg_le D (p default))
  have hmeas : ∀ (u : Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D)
      (α : Fin D.k → _root_.MIPStarRE.QPBT.DirectScalarQ D),
      ((_root_.MIPStarRE.QPBT.directCombinedStrategy D S).A
          (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D.combined (_root_.MIPStarRE.QPBT.combinedPoint u α))).postprocess
        (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero D.combined) =
        ((S.A (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)).postprocess
          (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero D)).postprocess
          (fun b _ => ∑ r : Fin D.k, α r * b r) := by
    intro u α
    show ((S.A (_root_.MIPStarRE.QPBT.directCombinedMeasuredQuestion D
        (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D.combined (_root_.MIPStarRE.QPBT.combinedPoint u α)))).postprocess
        (_root_.MIPStarRE.QPBT.directCombinedAnswerMap D
          (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D.combined (_root_.MIPStarRE.QPBT.combinedPoint u α)))).postprocess
        (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero D.combined) = _
    refine Eq.trans (_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_comp _ _ _) ?_
    refine Eq.trans ?_ (_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_comp
      (S.A (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)) (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero D)
      (fun b (_ : Fin D.combined.k) => ∑ r : Fin D.k, α r * b r)).symm
    rw [directCombinedMeasuredQuestion_point]
    exact congrArg (fun h => (S.A (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)).postprocess h)
      (directCombinedPointAnswerMap_comp D u α)
  have hgoalEq : _root_.MIPStarRE.QPBT.consistencyDefect
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
      (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron
        (((S.A (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)).postprocess
          (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero D)).effect outcome) 1)
      (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron 1
        (((GB.postprocess (_root_.MIPStarRE.QPBT.directTupleOfCombinedTuple D)).postprocess
          (_root_.MIPStarRE.QPBT.evalDirectPolyTupleAt u)).effect outcome)) S.ψ =
      _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
        (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron
          (((S.A (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)).postprocess
            (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero D)).effect outcome) 1)
        (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron 1
          ((GB.postprocess (fun p =>
            _root_.MIPStarRE.QPBT.evalDirectPolyTupleAt u (_root_.MIPStarRE.QPBT.directTupleOfCombinedTuple D p))).effect
              outcome)) S.ψ := by
    refine _root_.MIPStarRE.QPBT.consistencyDefect_congr _ _ _ _ _ _ (fun u a => rfl) fun u a => ?_
    rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_comp]
  rw [hgoalEq]
  refine le_trans hkey (le_of_eq (congrArg
    (fun x : ℝ => x + ((D.combined.m * D.d : ℕ) : ℝ) / D.q) ?_))
  rw [← _root_.MIPStarRE.QPBT.consistencyDefect_uniform_question_equiv (_root_.MIPStarRE.QPBT.directCombinedPointEquiv D)
    (fun z outcome => _root_.MIPStarRE.QPBT.heteroKron
      ((((_root_.MIPStarRE.QPBT.directCombinedStrategy D S).A
        (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D.combined z)).postprocess
          (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero D.combined)).effect outcome) 1)
    (fun z outcome => _root_.MIPStarRE.QPBT.heteroKron 1
      ((GB.postprocess (_root_.MIPStarRE.QPBT.evalDirectPolyTupleAt (D := D.combined) z)).effect
        outcome)) S.ψ]
  refine _root_.MIPStarRE.QPBT.consistencyDefect_congr _ _ _ _ _ _ (fun z r => ?_) fun z r => rfl
  exact congrArg (fun M => _root_.MIPStarRE.QPBT.heteroKron (M.effect r) (1 : _root_.LIDT.MIPStarRE.Quantum.Op S.ιB))
    (hmeas z.1 z.2).symm
