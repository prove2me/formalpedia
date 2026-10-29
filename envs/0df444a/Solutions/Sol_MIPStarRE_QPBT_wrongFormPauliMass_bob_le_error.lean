-- Prove2me | solution 1 for MIPStarRE.QPBT.wrongFormPauliMass_bob_le_error
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:49:50.853275+00:00
-- url     : https://prove2.me/submissions/d349e2a8-115c-43ec-9377-97b705816403

-- Generated proof for MIPStarRE.QPBT.wrongFormPauliMass_bob_le_error.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_Averages
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_LowDegree
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_MagicSquare
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Theorems.Thm_LIDT_MIPStarRE_LDT_Distribution_IsProbability_map
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_avgOver_uniform_fixed_le_card_mul_prod
import Theorems.Thm_MIPStarRE_QPBT_outcome_event_weight_mono
import Theorems.Thm_MIPStarRE_QPBT_rejectionMass_eq_one_sub_value
import Theorems.Thm_MIPStarRE_QPBT_sum_outcome_weight_left

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

/- Source helpers from QPBT/Games/Defs.lean. -/
/-!
# Games, tensor-product strategies, and value

This file provides the finite game carrier used by the Pauli basis test.  Pure
states are vectors in `EuclideanSpace`, and POVMs use the project's matrix
`Measurement` structure.

## References

The source-facing nodes are blueprint `def:game`, `def:povm-conventions`,
`def:tensor-product-strategy`, and `def:tensor-product-value`.
The paper origin is `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:10-57`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.Quantum



attribute [instance] _root_.MIPStarRE.QPBT.Game.questionAFintype _root_.MIPStarRE.QPBT.Game.questionBFintype
  _root_.MIPStarRE.QPBT.Game.answerAFintype _root_.MIPStarRE.QPBT.Game.answerBFintype _root_.MIPStarRE.QPBT.Game.questionADecidableEq
  _root_.MIPStarRE.QPBT.Game.questionBDecidableEq _root_.MIPStarRE.QPBT.Game.answerADecidableEq _root_.MIPStarRE.QPBT.Game.answerBDecidableEq









attribute [instance] _root_.MIPStarRE.QPBT.Strategy.ιAFintype _root_.MIPStarRE.QPBT.Strategy.ιBFintype
  _root_.MIPStarRE.QPBT.Strategy.ιADecidableEq _root_.MIPStarRE.QPBT.Strategy.ιBDecidableEq



/-! ### Algebra of the tensor placement

The shared tensor-placement API.  These identities are used both by the perfect
Magic Square strategy (blueprint `thm:ms-from-ac`) and by the rigidity transfer
step (blueprint `thm:ms-rigidity`), so they live
with the definition rather than in either development. -/





















/- The Euclidean linear map is the shared action used by the value and distance
functionals.  Keeping it at the Euclidean-space level avoids accidentally
using the function-space supremum norm of `Matrix.mulVec`. -/














/-- Every answer-pair Born weight is nonnegative.  This is formalization-only
support for the probability expression in `def:tensor-product-value`. -/
theorem outcomeWeight_nonneg {G : _root_.MIPStarRE.QPBT.Game} (S : _root_.MIPStarRE.QPBT.Strategy G)
    (x : G.QuestionA) (y : G.QuestionB) (a : G.AnswerA) (b : G.AnswerB) :
    0 ≤ _root_.MIPStarRE.QPBT.outcomeWeight S x y a b := by
  unfold _root_.MIPStarRE.QPBT.outcomeWeight _root_.MIPStarRE.QPBT.applyOperatorToState _root_.MIPStarRE.QPBT.heteroKron
  exact
    (Matrix.isPositive_toEuclideanLin_iff.mpr
      (Matrix.nonneg_iff_posSemidef.mp
        (_root_.LIDT.MIPStarRE.Quantum.kronecker_nonneg ((S.A x).pos a) ((S.B y).pos b)))).re_inner_nonneg_right S.ψ










/-- Every answer event has nonnegative Born weight. -/
theorem outcome_event_weight_nonneg {G : _root_.MIPStarRE.QPBT.Game} (S : _root_.MIPStarRE.QPBT.Strategy G)
    (x : G.QuestionA) (y : G.QuestionB)
    (E : G.AnswerA → G.AnswerB → Prop) [DecidableRel E] :
    0 ≤ _root_.MIPStarRE.QPBT.outcomeEventWeight S x y E := by
  unfold _root_.MIPStarRE.QPBT.outcomeEventWeight
  exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by
    split_ifs
    · exact _root_.MIPStarRE.QPBT.outcomeWeight_nonneg S x y a b
    · exact le_rfl



/-- An answer event depending only on Bob has its Bob marginal weight. -/
theorem outcome_event_weight_right_eq {G : _root_.MIPStarRE.QPBT.Game} (S : _root_.MIPStarRE.QPBT.Strategy G)
    (x : G.QuestionA) (y : G.QuestionB)
    (E : G.AnswerB → Prop) [DecidablePred E] :
    _root_.MIPStarRE.QPBT.outcomeEventWeight S x y (fun _ b => E b) = _root_.MIPStarRE.QPBT.bobEventWeight S y E := by
  unfold _root_.MIPStarRE.QPBT.outcomeEventWeight _root_.MIPStarRE.QPBT.bobEventWeight
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : E b
  · simp [hb, _root_.MIPStarRE.QPBT.sum_outcome_weight_left S x y b]
  · simp [hb]










end MIPStarRE.QPBT

/- Source helpers from QPBT/Games/DistanceTheorems/Support.lean. -/
/-!
# Finite-dimensional operator estimates for state-dependent distance

This module contains finite-dimensional operator and finite-sum identities used
by the paper-facing distance theorems. It introduces no new mathematical
assumptions or source-facing statements.

## References

- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-395`
- `references/ldt-paper/preliminaries.tex:649-666`
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.DistanceCalculus

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective



























/-- The state quadratic form is additive over finite sums of operators. This is
the formalization-only identity `lem:distance-qform-finset-sum`, used to expand
the relabeled overlaps in `lem:ld-sandwich`; detailed source proof
`references/neexp-paper/05_quantum_preliminaries.tex:952-999`. -/
theorem stateQForm_finset_sum {β ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (s : Finset β) (M : β → _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (∑ b ∈ s, M b) = ∑ b ∈ s, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (M b) := by
  simp [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, _root_.MIPStarRE.QPBT.applyOperatorToState]































































end MIPStarRE.QPBT.DistanceCalculus

/- Source helpers from QPBT/Observables/WinImplications/Averages.lean. -/
/-!
# Averaging lemmas for winning implications

This module derives the finite conditioning and fixed-edge rejection bounds
used by all seven exact winning implications.

## References

The formalization-only averaging and conditioning auxiliaries support items 1–7
of `lem:qld-win-implications`
from `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:192-267`
and blueprint `lem:qld-win-implications` and `lem:qld-win-implications-obs`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace WinImplications

scoped instance pauliEdgeNonempty : Nonempty _root_.MIPStarRE.QPBT.PauliEdge := _root_.MIPStarRE.QPBT.pauliEdge_nonempty



















/-- Rejection mass at every fixed edge and seed is nonnegative. -/
theorem pauliRejectionAt_nonneg {P : _root_.MIPStarRE.QPBT.AdmissibleParams}
    (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.pauliBasisTest P)) (e : _root_.MIPStarRE.QPBT.PauliEdge) (z : _root_.MIPStarRE.QPBT.PauliSpace P) :
    0 ≤ _root_.MIPStarRE.QPBT.WinImplications.pauliRejectionAt S e z := by
  exact _root_.MIPStarRE.QPBT.outcome_event_weight_nonneg S _ _ _

/-- Formalization-only auxiliary for items 1–7 of `lem:qld-win-implications`:
the average rejection mass of a finite game is one minus its value. -/
theorem rejectionEventAverage_eq_one_sub_value {G : _root_.MIPStarRE.QPBT.Game} (S : _root_.MIPStarRE.QPBT.Strategy G) :
    _root_.LIDT.MIPStarRE.LDT.avgOver G.μ (fun questions =>
      _root_.MIPStarRE.QPBT.outcomeEventWeight S questions.1 questions.2 fun a b =>
        G.decide questions.1 questions.2 a b = false) =
      1 - S.value := by
  classical
  simpa only [_root_.MIPStarRE.QPBT.outcomeEventWeight, Bool.eq_false_iff, ite_not] using
    _root_.MIPStarRE.QPBT.rejectionMass_eq_one_sub_value S






end WinImplications

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Test/Soundness/RawOperatorTransferCore.lean. -/
/-!
# Transfer from completed to raw Pauli effects

The extraction proof uses the complete Pauli-register measurement obtained by
folding malformed answers into outcome zero. The source theorem instead
compares the raw effects attached to answers of the form `.pauliOutcome u`.
This module bounds the malformed-answer mass by rejection on the two oriented
point/Pauli edges and transfers the completed-family estimates to the raw
families without adding a hypothesis to the source theorem.

## References

Paper `thm:pauli`,
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1431-1445`,
and its proof at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1862-1876`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section



namespace WinImplications

/-- A strategy winning with probability at least `1 - ε` has average Pauli-edge
rejection probability at most `ε`. -/
theorem pauliRejectionAverage_le_error_of_win {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}
    (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.pauliBasisTest P)) (hwin : 1 - ε ≤ S.value) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliEdge × _root_.MIPStarRE.QPBT.PauliSpace P))
        (fun ez => _root_.MIPStarRE.QPBT.WinImplications.pauliRejectionAt S ez.1 ez.2) ≤ ε := by
  classical
  have havg : _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliEdge × _root_.MIPStarRE.QPBT.PauliSpace P))
      (fun ez => _root_.MIPStarRE.QPBT.WinImplications.pauliRejectionAt S ez.1 ez.2) = 1 - S.value := by
    rw [← _root_.MIPStarRE.QPBT.WinImplications.rejectionEventAverage_eq_one_sub_value S]
    unfold _root_.MIPStarRE.QPBT.pauliBasisTest _root_.MIPStarRE.QPBT.pauliQuestionDistribution
    rw [_root_.LIDT.MIPStarRE.LDT.Distribution.avgOver_map]
    rfl
  rw [havg]
  linarith

/-- Rejection on one fixed oriented edge is at most the number of edge types
times the total rejection probability. -/
theorem fixedEdgeRejection_le_error_of_win {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}
    (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.pauliBasisTest P)) (hwin : 1 - ε ≤ S.value) (e : _root_.MIPStarRE.QPBT.PauliEdge) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliSpace P)) (_root_.MIPStarRE.QPBT.WinImplications.pauliRejectionAt S e) ≤
      (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ) * ε := by
  calc
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliSpace P)) (_root_.MIPStarRE.QPBT.WinImplications.pauliRejectionAt S e) ≤
        (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ) *
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliEdge × _root_.MIPStarRE.QPBT.PauliSpace P))
            (fun ez => _root_.MIPStarRE.QPBT.WinImplications.pauliRejectionAt S ez.1 ez.2) := by
      exact _root_.MIPStarRE.QPBT.WinImplications.avgOver_uniform_fixed_le_card_mul_prod _
        (fun edge z => _root_.MIPStarRE.QPBT.WinImplications.pauliRejectionAt_nonneg S edge z) e
    _ ≤ (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ) * ε := by
      exact mul_le_mul_of_nonneg_left (_root_.MIPStarRE.QPBT.WinImplications.pauliRejectionAverage_le_error_of_win S hwin)
        (Nat.cast_nonneg _)

end WinImplications

open DistanceCalculus

















































end

end MIPStarRE.QPBT

/-!
# Transfer from completed to raw Pauli effects

The extraction proof uses the complete Pauli-register measurement obtained by
folding malformed answers into outcome zero. The source theorem instead
compares the raw effects attached to answers of the form `.pauliOutcome u`.
This module bounds the malformed-answer mass by rejection on the two oriented
point/Pauli edges and transfers the completed-family estimates to the raw
families without adding a hypothesis to the source theorem.

## References

Paper `thm:pauli`,
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1431-1445`,
and its proof at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1862-1876`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum





open MIPStarRE.QPBT.WinImplications







open MIPStarRE.QPBT.DistanceCalculus

theorem solution {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}
    (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.pauliBasisTest P)) (hwin : 1 - ε ≤ S.value) (W : _root_.MIPStarRE.QPBT.PauliKind) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.ψ
        (_root_.MIPStarRE.QPBT.heteroKron 1
          (_root_.MIPStarRE.QPBT.ProjectiveSetting.wrongFormEffect (.pauli W) (S.B (_root_.MIPStarRE.QPBT.pauliQuestion P W)))) ≤
      (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ) * ε := by
  have hpoint (z : _root_.MIPStarRE.QPBT.PauliSpace P) :
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.ψ
          (_root_.MIPStarRE.QPBT.heteroKron 1
            (_root_.MIPStarRE.QPBT.ProjectiveSetting.wrongFormEffect (.pauli W) (S.B (_root_.MIPStarRE.QPBT.pauliQuestion P W)))) ≤
        _root_.MIPStarRE.QPBT.WinImplications.pauliRejectionAt S (_root_.MIPStarRE.QPBT.WinImplications.pointPauliEdge W) z := by
    have hmass :
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.ψ
            (_root_.MIPStarRE.QPBT.heteroKron 1
              (_root_.MIPStarRE.QPBT.ProjectiveSetting.wrongFormEffect (.pauli W)
                (S.B (_root_.MIPStarRE.QPBT.pauliQuestion P W)))) =
          _root_.MIPStarRE.QPBT.bobEventWeight S (_root_.MIPStarRE.QPBT.pauliQuestion P W)
            (fun b => _root_.MIPStarRE.QPBT.validPauliAnswer (.pauli W) b = false) := by
      unfold _root_.MIPStarRE.QPBT.ProjectiveSetting.wrongFormEffect _root_.MIPStarRE.QPBT.bobEventWeight
      rw [_root_.MIPStarRE.QPBT.DistanceCalculus.heteroKron_finset_sum_right, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_finset_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : _root_.MIPStarRE.QPBT.validPauliAnswer (.pauli W) b = false
      · simp [hb, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, _root_.MIPStarRE.QPBT.bobOutcomeWeight]
      · simp [hb]
    rw [hmass]
    rw [← _root_.MIPStarRE.QPBT.outcome_event_weight_right_eq S
      ((.point W), _root_.MIPStarRE.QPBT.pauliCL P (.point W) z) (_root_.MIPStarRE.QPBT.pauliQuestion P W)]
    unfold _root_.MIPStarRE.QPBT.WinImplications.pauliRejectionAt _root_.MIPStarRE.QPBT.WinImplications.pauliSourceQuestions
    simp only [_root_.MIPStarRE.QPBT.WinImplications.pointPauliEdge, _root_.MIPStarRE.QPBT.pauliCL, _root_.MIPStarRE.QPBT.pauliQuestion]
    apply _root_.MIPStarRE.QPBT.outcome_event_weight_mono
    intro a b hb
    simp [_root_.MIPStarRE.QPBT.pauliWinPredicate, hb]
  calc
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.ψ
        (_root_.MIPStarRE.QPBT.heteroKron 1
          (_root_.MIPStarRE.QPBT.ProjectiveSetting.wrongFormEffect (.pauli W) (S.B (_root_.MIPStarRE.QPBT.pauliQuestion P W)))) =
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliSpace P)) (fun _ =>
          _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.ψ
            (_root_.MIPStarRE.QPBT.heteroKron 1
              (_root_.MIPStarRE.QPBT.ProjectiveSetting.wrongFormEffect (.pauli W)
                (S.B (_root_.MIPStarRE.QPBT.pauliQuestion P W))))) := by
      symm
      exact _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_const _
    _ ≤ _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliSpace P))
        (_root_.MIPStarRE.QPBT.WinImplications.pauliRejectionAt S (_root_.MIPStarRE.QPBT.WinImplications.pointPauliEdge W)) := by
      exact _root_.LIDT.MIPStarRE.LDT.avgOver_mono _ _ _ hpoint
    _ ≤ _ := _root_.MIPStarRE.QPBT.WinImplications.fixedEdgeRejection_le_error_of_win S hwin _
