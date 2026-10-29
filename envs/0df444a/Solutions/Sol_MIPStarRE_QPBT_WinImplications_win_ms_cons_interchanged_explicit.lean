-- Prove2me | solution 1 for MIPStarRE.QPBT.WinImplications.win_ms_cons_interchanged_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T02:22:38.902245+00:00
-- url     : https://prove2.me/submissions/e5ef02e8-0f4f-45eb-b70e-205f3376621f

-- Generated proof for MIPStarRE.QPBT.WinImplications.win_ms_cons_interchanged_explicit.
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
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Observables_Anticommuting
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_Approx
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_Averages
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_Commuting
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_Interchange
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_LowDegree
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_MagicSquare
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_Setup
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_MagicSquare
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_LIDT_MIPStarRE_LDT_Distribution_IsProbability_map
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_avgOver_anticomm_le_sixteen_mul_gated
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_avgOver_uniform_fixed_le_card_mul_prod
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_msConsConsistency_eq_mismatch_interchanged
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_pointMsMismatch_le_rejection_interchanged
import Theorems.Thm_MIPStarRE_QPBT_rejectionMass_eq_one_sub_value

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
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














end MIPStarRE.QPBT

/- Source helpers from QPBT/Observables/WinImplications/Commuting.lean. -/
/-!
# Commuting winning implications

This module proves the exact Pair/W and point-trace consistency bounds on
commuting Pauli tuples.

## References

The commuting-tuple consistency theorems prove items 4 and 5
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



















/-- The point coordinate of the low-degree projection is the selected shared block. -/
theorem pauliToLd_point_eq_selected (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (W : _root_.MIPStarRE.QPBT.PauliKind)
    (z : _root_.MIPStarRE.QPBT.PauliSpace P) :
    (_root_.MIPStarRE.QPBT.pauliToLd P W z).point = _root_.MIPStarRE.QPBT.WinImplications.selectedTuplePoint W (_root_.MIPStarRE.QPBT.WinImplications.pauliSharedSplit P z).1 := by
  funext i
  cases W <;> rfl












end WinImplications

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Observables/WinImplications/LowDegree.lean. -/
attribute [local instance] _root_.MIPStarRE.QPBT.WinImplications.instDecidableRel_qPBT
attribute [local instance] _root_.MIPStarRE.QPBT.WinImplications.linePointFintypeCanonical
/-!
# Low-degree winning implications

This module proves the exact line-point and Pauli-basis consistency bounds.

## References

The line-point and Pauli-basis consistency theorems prove items 2 and 3
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

















/-- Uniform Pauli seeds have the uniform shared-tuple marginal. -/
theorem avgOver_pauliTuple_uniform (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (f : _root_.MIPStarRE.QPBT.PauliTuple P → ℝ) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliSpace P))
        (fun z => f (_root_.MIPStarRE.QPBT.WinImplications.pauliSharedSplit P z).1) =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliTuple P)) f := by
  exact _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_equiv_fst (_root_.MIPStarRE.QPBT.WinImplications.pauliSharedSplit P) f



/-- The point conditioning map produces the typed point content. -/
theorem pauliCL_point_eq (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (W : _root_.MIPStarRE.QPBT.PauliKind)
    (z : _root_.MIPStarRE.QPBT.PauliSpace P) :
    _root_.MIPStarRE.QPBT.pauliCL P (.point W) z =
      _root_.MIPStarRE.QPBT.ProjectiveSetting.contentOfPoint P W (_root_.MIPStarRE.QPBT.pauliToLd P W z).point := by
  funext i
  rcases i with ((((j | j) | u) | j) | u) | u <;> cases W <;> rfl

/-- The shared conditioning map produces the typed tuple content. -/
theorem pauliCL_shared_eq (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (t : _root_.MIPStarRE.QPBT.PauliType)
    (ht : _root_.MIPStarRE.QPBT.pauliCL P t = _root_.MIPStarRE.QPBT.pauliSharedProjection) (z : _root_.MIPStarRE.QPBT.PauliSpace P) :
    _root_.MIPStarRE.QPBT.pauliCL P t z = _root_.MIPStarRE.QPBT.ProjectiveSetting.contentOfTuple P
      (_root_.MIPStarRE.QPBT.pauliXBlock z) (_root_.MIPStarRE.QPBT.pauliZBlock z) (_root_.MIPStarRE.QPBT.pauliRXBlock z) (_root_.MIPStarRE.QPBT.pauliRZBlock z) := by
  rw [ht]
  funext i
  rcases i with ((((j | j) | u) | j) | u) | u <;> rfl






































































end WinImplications

end

end MIPStarRE.QPBT

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

/-- Winning bounds the global rejection average. -/
theorem pauliRejectionAverage_le_error {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliEdge × _root_.MIPStarRE.QPBT.PauliSpace P))
        (fun ez => _root_.MIPStarRE.QPBT.WinImplications.pauliRejectionAt S.toStrategy ez.1 ez.2) ≤ ε := by
  have havg : _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliEdge × _root_.MIPStarRE.QPBT.PauliSpace P))
      (fun ez => _root_.MIPStarRE.QPBT.WinImplications.pauliRejectionAt S.toStrategy ez.1 ez.2) =
      1 - S.toStrategy.value := by
    rw [← _root_.MIPStarRE.QPBT.WinImplications.rejectionEventAverage_eq_one_sub_value S.toStrategy]
    unfold _root_.MIPStarRE.QPBT.pauliBasisTest _root_.MIPStarRE.QPBT.pauliQuestionDistribution
    rw [_root_.LIDT.MIPStarRE.LDT.Distribution.avgOver_map]
    rfl
  rw [havg]
  linarith [S.win]

/-- Fixing one verifier edge costs at most the cardinality of the finite edge graph. -/
theorem fixedEdgeRejection_le_error {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (e : _root_.MIPStarRE.QPBT.PauliEdge) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliSpace P)) (_root_.MIPStarRE.QPBT.WinImplications.pauliRejectionAt S.toStrategy e) ≤
      (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ) * ε := by
  calc
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliSpace P)) (_root_.MIPStarRE.QPBT.WinImplications.pauliRejectionAt S.toStrategy e) ≤
        (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ) *
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliEdge × _root_.MIPStarRE.QPBT.PauliSpace P))
            (fun ez => _root_.MIPStarRE.QPBT.WinImplications.pauliRejectionAt S.toStrategy ez.1 ez.2) := by
      exact _root_.MIPStarRE.QPBT.WinImplications.avgOver_uniform_fixed_le_card_mul_prod _
        (fun edge z => _root_.MIPStarRE.QPBT.WinImplications.pauliRejectionAt_nonneg S.toStrategy edge z) e
    _ ≤ (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ) * ε := by
      exact mul_le_mul_of_nonneg_left (_root_.MIPStarRE.QPBT.WinImplications.pauliRejectionAverage_le_error S)
        (Nat.cast_nonneg _)


end WinImplications

end

end MIPStarRE.QPBT

/-!
# Approximate winning implications for the tuple subtests

This module proves the operator-distance companions, with their
factor-interchanged forms, of the commutation check, the commutation
consistency check, and the Magic Square consistency check.

## References

The declarations support the trailing clause of `lem:qld-win-implications` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:614-702`. Their paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:192-267`,
whose closing sentences at lines 227 and 263-264 state both companions.
-/



open scoped BigOperators Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum



open MIPStarRE.QPBT.WinImplications



/-! ## Commutation check -/











/-! ## Commutation consistency check -/











/-! ## Magic square consistency check -/
attribute [local instance] _root_.MIPStarRE.QPBT.WinImplications.pauliEdgeNonemptyApprox

theorem solution :
    ∀ (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (ε : ℝ) (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε),
      0 ≤ ε → ∀ W : _root_.MIPStarRE.QPBT.PauliKind,
      _root_.MIPStarRE.QPBT.consistencyDefect (_root_.MIPStarRE.QPBT.anticommTupleDist P)
        (fun ω a => _root_.MIPStarRE.QPBT.heteroKron
          ((S.msVarBitMeas .alice (_root_.MIPStarRE.QPBT.WinImplications.selectedMsVar W) ω).effect a) 1)
        (fun ω a => _root_.MIPStarRE.QPBT.heteroKron 1
          ((S.pointTraceMeas .bob W (_root_.MIPStarRE.QPBT.WinImplications.selectedTuplePoint W ω)
            (_root_.MIPStarRE.QPBT.WinImplications.selectedTupleScalar W ω)).effect a))
        S.toStrategy.ψ ≤ 16 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ) * ε := by
  intro P ε S _ W
  rw [_root_.MIPStarRE.QPBT.WinImplications.msConsConsistency_eq_mismatch_interchanged]
  calc
    _ ≤ 16 * _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliTuple P)) (fun ω =>
        if _root_.MIPStarRE.QPBT.IsAnticommuting ω then
          _root_.MIPStarRE.QPBT.outcomeEventWeight S.toStrategy
            (_root_.MIPStarRE.QPBT.ProjectiveSetting.msQuestion P (.var (_root_.MIPStarRE.QPBT.WinImplications.selectedMsVar W))
              ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
            (_root_.MIPStarRE.QPBT.ProjectiveSetting.pointQuestion P W (_root_.MIPStarRE.QPBT.WinImplications.selectedTuplePoint W ω))
            (fun A B => _root_.MIPStarRE.QPBT.ProjectiveSetting.pairWAnswerOrZero A ≠
              _root_.MIPStarRE.QPBT.WinImplications.pointTraceLabel P W ω B)
        else 0) := by
      apply _root_.MIPStarRE.QPBT.WinImplications.avgOver_anticomm_le_sixteen_mul_gated
      intro ω
      exact _root_.MIPStarRE.QPBT.outcome_event_weight_nonneg S.toStrategy _ _ _
    _ ≤ 16 * _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliSpace P))
        (_root_.MIPStarRE.QPBT.WinImplications.pauliRejectionAt S.toStrategy (_root_.MIPStarRE.QPBT.WinImplications.msVarPointEdge W)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [← _root_.MIPStarRE.QPBT.WinImplications.avgOver_pauliTuple_uniform]
      apply _root_.LIDT.MIPStarRE.LDT.avgOver_mono
      intro z
      by_cases hanti : _root_.MIPStarRE.QPBT.IsAnticommuting (_root_.MIPStarRE.QPBT.WinImplications.pauliSharedSplit P z).1
      · simp only [if_pos hanti]
        have hs := _root_.MIPStarRE.QPBT.WinImplications.pointMsMismatch_le_rejection_interchanged S W z hanti
        rw [_root_.MIPStarRE.QPBT.WinImplications.pauliCL_point_eq,
          _root_.MIPStarRE.QPBT.WinImplications.pauliCL_shared_eq P (.ms (.var (_root_.MIPStarRE.QPBT.WinImplications.selectedMsVar W))) rfl] at hs
        rw [_root_.MIPStarRE.QPBT.WinImplications.pauliToLd_point_eq_selected] at hs
        simpa [_root_.MIPStarRE.QPBT.WinImplications.pauliSharedSplit, _root_.MIPStarRE.QPBT.WinImplications.selectedTuplePoint, _root_.MIPStarRE.QPBT.WinImplications.selectedMsVar,
          _root_.MIPStarRE.QPBT.ProjectiveSetting.pointQuestion, _root_.MIPStarRE.QPBT.ProjectiveSetting.msQuestion]
          using hs
      · simp only [if_neg hanti]
        exact _root_.MIPStarRE.QPBT.WinImplications.pauliRejectionAt_nonneg S.toStrategy _ z
    _ ≤ 16 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ) * ε := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (_root_.MIPStarRE.QPBT.WinImplications.fixedEdgeRejection_le_error S _)
        (by norm_num)
