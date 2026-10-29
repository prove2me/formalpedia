-- Prove2me | solution 1 for MIPStarRE.QPBT.point_self_consistency_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:20:47.908406+00:00
-- url     : https://prove2.me/submissions/217eb075-9e62-4374-90e1-2982ac64929d

-- Generated proof for MIPStarRE.QPBT.point_self_consistency_le.
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
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_PointConsistency
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_Averages
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_Consistency
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_LowDegree
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_MagicSquare
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_LIDT_MIPStarRE_LDT_Distribution_IsProbability_map
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_avgOver_uniform_fixed_le_card_mul_prod
import Theorems.Thm_MIPStarRE_QPBT_outcome_event_weight_mono
import Theorems.Thm_MIPStarRE_QPBT_pointConsistency_eq_mismatch
import Theorems.Thm_MIPStarRE_QPBT_rejectionMass_eq_one_sub_value

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting
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

/- Source helpers from QPBT/Observables/WinImplications/Consistency.lean. -/
/-!
# Exact consistency winning implication

This module proves the exact same-question consistency bound for the two
players' Pauli-test measurements.

## References

The strategy consistency theorem proves item 1
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





/-- Unequal answers to the same sampled question are rejected on its self-loop.
This is the rejection event used for item 1 of `lem:qld-win-implications`, paper
`14_analysis_of_the_pauli_basis_test.tex:197-199`. -/
theorem loopMismatch_le_rejection {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (t : _root_.MIPStarRE.QPBT.PauliType) (z : _root_.MIPStarRE.QPBT.PauliSpace P) :
    _root_.MIPStarRE.QPBT.outcomeEventWeight S.toStrategy
        (t, _root_.MIPStarRE.QPBT.pauliCL P t z) (t, _root_.MIPStarRE.QPBT.pauliCL P t z) (fun A B => A ≠ B) ≤
      _root_.MIPStarRE.QPBT.WinImplications.pauliRejectionAt S.toStrategy (_root_.MIPStarRE.QPBT.WinImplications.pauliLoopEdge t) z := by
  unfold _root_.MIPStarRE.QPBT.WinImplications.pauliRejectionAt _root_.MIPStarRE.QPBT.WinImplications.pauliSourceQuestions _root_.MIPStarRE.QPBT.WinImplications.pauliLoopEdge
  dsimp
  apply _root_.MIPStarRE.QPBT.outcome_event_weight_mono
  intro A B hne
  simp only [_root_.MIPStarRE.QPBT.pauliWinPredicate, Bool.and_eq_true, ↓reduceIte,
    Bool.if_false_right, Bool.decide_and, Bool.decide_eq_true,
    Bool.and_eq_false_imp, decide_eq_false_iff_not, and_imp]
  intro _ _
  exact hne






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















/-- Uniform Pauli seeds have the uniform low-degree marginal in either basis. -/
theorem avgOver_pauliToLd_uniform (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (W : _root_.MIPStarRE.QPBT.PauliKind)
    (f : _root_.MIPStarRE.QPBT.LdSpace P.toLdParams → ℝ) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliSpace P)) (fun z => f (_root_.MIPStarRE.QPBT.pauliToLd P W z)) =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.LdSpace P.toLdParams)) f := by
  exact _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_equiv_fst (pauliLdSplit P W) f



/-- The point block of a uniform low-degree seed is uniform. -/
theorem avgOver_ldPoint_uniform (L : _root_.MIPStarRE.QPBT.LdParams)
    (f : (Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L) → ℝ) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.LdSpace L)) (fun z => f z.point) =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L)) f := by
  exact _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_equiv_fst (ldPointSplit L) f










































































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
# Expanded point consistency and commutation

This module records the quantitative conclusions for the expanded point
measurements on each of the four register placements. No symmetry-transfer
principle is assumed: the four placements occur explicitly in the statements.

## References

The declarations formalize blueprint
`lem:qld-comm-cons`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:452-505`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum





/-! ## Consistency of the unexpanded point measurements -/
attribute [local instance] _root_.MIPStarRE.QPBT.pauliEdgeNonemptyPointConsistency

theorem solution {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (W : _root_.MIPStarRE.QPBT.PauliKind) :
    _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
        (fun u a => _root_.MIPStarRE.QPBT.heteroKron ((S.pointMeas .alice W u).effect a) 1)
        (fun u a => _root_.MIPStarRE.QPBT.heteroKron 1 ((S.pointMeas .bob W u).effect a))
        S.toStrategy.ψ ≤ (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ) * ε := by
  rw [_root_.MIPStarRE.QPBT.pointConsistency_eq_mismatch]
  have hsource :
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)) (fun u =>
          _root_.MIPStarRE.QPBT.outcomeEventWeight S.toStrategy
            (_root_.MIPStarRE.QPBT.ProjectiveSetting.pointQuestion P W u)
            (_root_.MIPStarRE.QPBT.ProjectiveSetting.pointQuestion P W u)
            (fun A B => _root_.MIPStarRE.QPBT.ProjectiveSetting.pointAnswerOrZero A ≠
              _root_.MIPStarRE.QPBT.ProjectiveSetting.pointAnswerOrZero B)) =
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliSpace P)) (fun z =>
          _root_.MIPStarRE.QPBT.outcomeEventWeight S.toStrategy
            (_root_.MIPStarRE.QPBT.ProjectiveSetting.pointQuestion P W (_root_.MIPStarRE.QPBT.pauliToLd P W z).point)
            (_root_.MIPStarRE.QPBT.ProjectiveSetting.pointQuestion P W (_root_.MIPStarRE.QPBT.pauliToLd P W z).point)
            (fun A B => _root_.MIPStarRE.QPBT.ProjectiveSetting.pointAnswerOrZero A ≠
              _root_.MIPStarRE.QPBT.ProjectiveSetting.pointAnswerOrZero B)) := by
    let g : (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) → ℝ := fun u =>
      _root_.MIPStarRE.QPBT.outcomeEventWeight S.toStrategy
        (_root_.MIPStarRE.QPBT.ProjectiveSetting.pointQuestion P W u)
        (_root_.MIPStarRE.QPBT.ProjectiveSetting.pointQuestion P W u)
        (fun A B => _root_.MIPStarRE.QPBT.ProjectiveSetting.pointAnswerOrZero A ≠
          _root_.MIPStarRE.QPBT.ProjectiveSetting.pointAnswerOrZero B)
    have hld := _root_.MIPStarRE.QPBT.WinImplications.avgOver_pauliToLd_uniform P W (fun z => g z.point)
    have hpoint := _root_.MIPStarRE.QPBT.WinImplications.avgOver_ldPoint_uniform P.toLdParams g
    exact (hld.trans hpoint).symm
  rw [hsource]
  calc
    _ ≤ _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliSpace P))
        (_root_.MIPStarRE.QPBT.WinImplications.pauliRejectionAt S.toStrategy
          (_root_.MIPStarRE.QPBT.WinImplications.pauliLoopEdge (.point W))) := by
      apply _root_.LIDT.MIPStarRE.LDT.avgOver_mono
      intro z
      refine le_trans ?_
        (_root_.MIPStarRE.QPBT.WinImplications.loopMismatch_le_rejection S (.point W) z)
      apply _root_.MIPStarRE.QPBT.outcome_event_weight_mono
      intro A B hne hAB
      exact hne (congrArg _root_.MIPStarRE.QPBT.ProjectiveSetting.pointAnswerOrZero hAB)
    _ ≤ (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ) * ε :=
      _root_.MIPStarRE.QPBT.WinImplications.fixedEdgeRejection_le_error S _
