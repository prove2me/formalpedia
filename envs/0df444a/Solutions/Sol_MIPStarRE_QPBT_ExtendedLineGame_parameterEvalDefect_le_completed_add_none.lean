-- Prove2me | solution 1 for MIPStarRE.QPBT.ExtendedLineGame.parameterEvalDefect_le_completed_add_none
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:32:14.401994+00:00
-- url     : https://prove2.me/submissions/cc4b9b67-9a69-4856-95c0-dd577ca0da62

-- Generated proof for MIPStarRE.QPBT.ExtendedLineGame.parameterEvalDefect_le_completed_add_none.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
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
import Definitions.Def_QPBT_QPBT_Algebra_Coefficients
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame_ParameterCompletion
import Definitions.Def_QPBT_QPBT_Games_Defs
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_evalCoefficient_ne_imp_directEvalOpt_ne_or_eq_none
import Theorems.Thm_MIPStarRE_QPBT_sum_outcome_weight_left
import Theorems.Thm_MIPStarRE_QPBT_sum_outcome_weight_right

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.ExtendedLineGame
end MIPStarRE.QPBT.ExtendedLineGame

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












/-- An answer event depending only on Alice has its Alice marginal weight. -/
theorem outcome_event_weight_left_eq {G : _root_.MIPStarRE.QPBT.Game} (S : _root_.MIPStarRE.QPBT.Strategy G)
    (x : G.QuestionA) (y : G.QuestionB)
    (E : G.AnswerA → Prop) [DecidablePred E] :
    _root_.MIPStarRE.QPBT.outcomeEventWeight S x y (fun a _ => E a) = _root_.MIPStarRE.QPBT.aliceEventWeight S x E := by
  unfold _root_.MIPStarRE.QPBT.outcomeEventWeight _root_.MIPStarRE.QPBT.aliceEventWeight
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : E a
  · simp [ha, _root_.MIPStarRE.QPBT.sum_outcome_weight_right S x y a]
  · simp [ha]

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

/-!
# Parameter evaluation versus completed line evaluation

Completed evaluation of a coefficient vector may return `none`, notably on a
zero-direction line when the represented polynomial is not constant.  A
successful completed readout at the point represented by a parameter agrees
with ordinary coefficient evaluation at that parameter.  Consequently,
parameter-value disagreement is contained in the union of completed-readout
disagreement and the two failure events.

The final theorem lifts this inclusion to the Born weights of two arbitrary
strategy POVMs.  It uses neither projectivity nor a collision estimate.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:230-390`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1402`
-/



open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT



open MIPStarRE.QPBT.ExtendedLineGame

set_option maxHeartbeats 600000 in
-- Expanding three nested outcome events requires repeated finite-sum normalization.

theorem solution
    {G : _root_.MIPStarRE.QPBT.Game} {params : _root_.MIPStarRE.QPBT.DirectLdParams} {degree : ℕ}
    (S : _root_.MIPStarRE.QPBT.Strategy G) (questionA : G.QuestionA) (questionB : G.QuestionB)
    (readA : G.AnswerA → _root_.MIPStarRE.QPBT.DirectDegPoly params degree)
    (readB : G.AnswerB → _root_.MIPStarRE.QPBT.DirectDegPoly params degree)
    (line : _root_.MIPStarRE.QPBT.DirectLineDesc params) (parameter : _root_.MIPStarRE.QPBT.DirectScalarQ params) :
    _root_.MIPStarRE.QPBT.ExtendedLineGame.parameterEvalDefect S questionA questionB readA readB parameter ≤
      _root_.MIPStarRE.QPBT.ExtendedLineGame.completedEvalDefect S questionA questionB readA readB line parameter +
        _root_.MIPStarRE.QPBT.ExtendedLineGame.completedEvalNoneMassA S questionA readA line parameter +
        _root_.MIPStarRE.QPBT.ExtendedLineGame.completedEvalNoneMassB S questionB readB line parameter := by
  classical
  unfold _root_.MIPStarRE.QPBT.ExtendedLineGame.completedEvalNoneMassA _root_.MIPStarRE.QPBT.ExtendedLineGame.completedEvalNoneMassB
  rw [← _root_.MIPStarRE.QPBT.outcome_event_weight_left_eq S questionA questionB,
    ← _root_.MIPStarRE.QPBT.outcome_event_weight_right_eq S questionA questionB]
  unfold _root_.MIPStarRE.QPBT.ExtendedLineGame.parameterEvalDefect _root_.MIPStarRE.QPBT.ExtendedLineGame.completedEvalDefect _root_.MIPStarRE.QPBT.outcomeEventWeight
  calc
    (∑ answerA : G.AnswerA, ∑ answerB : G.AnswerB,
        if _root_.MIPStarRE.QPBT.evalCoefficient (readA answerA) parameter ≠
            _root_.MIPStarRE.QPBT.evalCoefficient (readB answerB) parameter then
          _root_.MIPStarRE.QPBT.outcomeWeight S questionA questionB answerA answerB else 0) ≤
      ∑ answerA : G.AnswerA, ∑ answerB : G.AnswerB,
        ((if _root_.MIPStarRE.QPBT.directEvalOpt line (line.base + parameter • line.direction)
              (readA answerA) ≠
            _root_.MIPStarRE.QPBT.directEvalOpt line (line.base + parameter • line.direction)
              (readB answerB) then
            _root_.MIPStarRE.QPBT.outcomeWeight S questionA questionB answerA answerB else 0) +
          (if _root_.MIPStarRE.QPBT.directEvalOpt line (line.base + parameter • line.direction)
              (readA answerA) = none then
            _root_.MIPStarRE.QPBT.outcomeWeight S questionA questionB answerA answerB else 0) +
          if _root_.MIPStarRE.QPBT.directEvalOpt line (line.base + parameter • line.direction)
              (readB answerB) = none then
            _root_.MIPStarRE.QPBT.outcomeWeight S questionA questionB answerA answerB else 0) := by
      apply Finset.sum_le_sum
      intro answerA _
      apply Finset.sum_le_sum
      intro answerB _
      have hweight := _root_.MIPStarRE.QPBT.outcomeWeight_nonneg S questionA questionB answerA answerB
      by_cases hparameter : _root_.MIPStarRE.QPBT.evalCoefficient (readA answerA) parameter ≠
          _root_.MIPStarRE.QPBT.evalCoefficient (readB answerB) parameter
      · rcases _root_.MIPStarRE.QPBT.ExtendedLineGame.evalCoefficient_ne_imp_directEvalOpt_ne_or_eq_none
          line (readA answerA) (readB answerB) parameter hparameter with
          hcompleted | hnoneA | hnoneB
        · simp [hparameter, hcompleted]
          split_ifs <;> linarith
        · simp [hparameter, hnoneA]
          split_ifs <;> linarith
        · simp [hparameter, hnoneB]
          split_ifs <;> linarith
      · simp [hparameter]
        split_ifs <;> linarith
    _ =
        (∑ answerA : G.AnswerA, ∑ answerB : G.AnswerB,
          if _root_.MIPStarRE.QPBT.directEvalOpt line (line.base + parameter • line.direction)
                (readA answerA) ≠
              _root_.MIPStarRE.QPBT.directEvalOpt line (line.base + parameter • line.direction)
                (readB answerB) then
            _root_.MIPStarRE.QPBT.outcomeWeight S questionA questionB answerA answerB else 0) +
        (∑ answerA : G.AnswerA, ∑ answerB : G.AnswerB,
          if _root_.MIPStarRE.QPBT.directEvalOpt line (line.base + parameter • line.direction)
              (readA answerA) = none then
            _root_.MIPStarRE.QPBT.outcomeWeight S questionA questionB answerA answerB else 0) +
        ∑ answerA : G.AnswerA, ∑ answerB : G.AnswerB,
          if _root_.MIPStarRE.QPBT.directEvalOpt line (line.base + parameter • line.direction)
              (readB answerB) = none then
            _root_.MIPStarRE.QPBT.outcomeWeight S questionA questionB answerA answerB else 0 := by
      simp_rw [Finset.sum_add_distrib]
