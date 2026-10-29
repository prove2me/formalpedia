-- Prove2me | solution 1 for MIPStarRE.QPBT.directLdRejectionProbability_eq_one_sub_value
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:32:14.240718+00:00
-- url     : https://prove2.me/submissions/9cb4f81a-bbce-4d88-82a4-70b162ea731f

-- Generated proof for MIPStarRE.QPBT.directLdRejectionProbability_eq_one_sub_value.
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
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_GameValue
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_outcomeWeight_sum_eq_one

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/DirectLowDegree/GameValue.lean. -/
/-!
# Rejection probabilities for the directly indexed low-degree game

This module compares the rejection probability of the directly indexed game
with the branch weights used by the low individual degree test.
All declarations below are formalization-only support derived from the game
value; none is a paper-labelled result.

## References

The uniform distribution on the three ordered question types is specified in
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:178-186`,
and its verifier is specified in the same file at lines 320-392.  The three
equal outer weights of the low individual degree test and its uniform role
choices are specified in `references/ldt-paper/test_definition.tex:10-67`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.Quantum

noncomputable section

private theorem directLdAccepted_add_rejected_eq_one
    (D : _root_.MIPStarRE.QPBT.DirectLdParams) (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.directLdGame D))
    (types : _root_.MIPStarRE.QPBT.LdType × _root_.MIPStarRE.QPBT.LdType) (sample : _root_.MIPStarRE.QPBT.DirectLdSpace D) :
    (∑ a : (_root_.MIPStarRE.QPBT.directLdGame D).AnswerA, ∑ b : (_root_.MIPStarRE.QPBT.directLdGame D).AnswerB,
        if _root_.MIPStarRE.QPBT.directLdWinPredicate D
            (types.1, _root_.MIPStarRE.QPBT.directLdMap D types.1 sample)
            (types.2, _root_.MIPStarRE.QPBT.directLdMap D types.2 sample) a b then
          _root_.MIPStarRE.QPBT.outcomeWeight S
            (types.1, _root_.MIPStarRE.QPBT.directLdMap D types.1 sample)
            (types.2, _root_.MIPStarRE.QPBT.directLdMap D types.2 sample) a b
        else 0) +
      (∑ a : (_root_.MIPStarRE.QPBT.directLdGame D).AnswerA, ∑ b : (_root_.MIPStarRE.QPBT.directLdGame D).AnswerB,
        if _root_.MIPStarRE.QPBT.directLdWinPredicate D
            (types.1, _root_.MIPStarRE.QPBT.directLdMap D types.1 sample)
            (types.2, _root_.MIPStarRE.QPBT.directLdMap D types.2 sample) a b then
          0
        else _root_.MIPStarRE.QPBT.outcomeWeight S
          (types.1, _root_.MIPStarRE.QPBT.directLdMap D types.1 sample)
          (types.2, _root_.MIPStarRE.QPBT.directLdMap D types.2 sample) a b) = 1 := by
  calc
    _ = ∑ a : (_root_.MIPStarRE.QPBT.directLdGame D).AnswerA, ∑ b : (_root_.MIPStarRE.QPBT.directLdGame D).AnswerB,
        _root_.MIPStarRE.QPBT.outcomeWeight S
          (types.1, _root_.MIPStarRE.QPBT.directLdMap D types.1 sample)
          (types.2, _root_.MIPStarRE.QPBT.directLdMap D types.2 sample) a b := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro b _
      by_cases h : _root_.MIPStarRE.QPBT.directLdWinPredicate D
          (types.1, _root_.MIPStarRE.QPBT.directLdMap D types.1 sample)
          (types.2, _root_.MIPStarRE.QPBT.directLdMap D types.2 sample) a b
      · simp [h]
      · simp [h]
    _ = 1 := _root_.MIPStarRE.QPBT.outcomeWeight_sum_eq_one S
      (types.1, _root_.MIPStarRE.QPBT.directLdMap D types.1 sample)
      (types.2, _root_.MIPStarRE.QPBT.directLdMap D types.2 sample)



















end

end MIPStarRE.QPBT

/-!
# Rejection probabilities for the directly indexed low-degree game

This module compares the rejection probability of the directly indexed game
with the branch weights used by the low individual degree test.
All declarations below are formalization-only support derived from the game
value; none is a paper-labelled result.

## References

The uniform distribution on the three ordered question types is specified in
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:178-186`,
and its verifier is specified in the same file at lines 320-392.  The three
equal outer weights of the low individual degree test and its uniform role
choices are specified in `references/ldt-paper/test_definition.tex:10-67`.
-/



open scoped BigOperators MatrixOrder Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.Quantum

theorem solution
    (D : _root_.MIPStarRE.QPBT.DirectLdParams) (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.directLdGame D)) :
    _root_.MIPStarRE.QPBT.directLdRejectionProbability D S = 1 - S.value := by
  let accepted : (_root_.MIPStarRE.QPBT.LdType × _root_.MIPStarRE.QPBT.LdType) → _root_.MIPStarRE.QPBT.DirectLdSpace D → ℝ :=
    fun types sample =>
      ∑ a : (_root_.MIPStarRE.QPBT.directLdGame D).AnswerA, ∑ b : (_root_.MIPStarRE.QPBT.directLdGame D).AnswerB,
        if _root_.MIPStarRE.QPBT.directLdWinPredicate D
            (types.1, _root_.MIPStarRE.QPBT.directLdMap D types.1 sample)
            (types.2, _root_.MIPStarRE.QPBT.directLdMap D types.2 sample) a b then
          _root_.MIPStarRE.QPBT.outcomeWeight S
            (types.1, _root_.MIPStarRE.QPBT.directLdMap D types.1 sample)
            (types.2, _root_.MIPStarRE.QPBT.directLdMap D types.2 sample) a b
        else 0
  have hbranch (types : _root_.MIPStarRE.QPBT.LdType × _root_.MIPStarRE.QPBT.LdType) :
      _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability D S types =
        1 - _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectLdSpace D)) (accepted types) := by
    rw [show _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability D S types =
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectLdSpace D))
          (fun sample => 1 - accepted types sample) by
      apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
      intro sample
      dsimp [accepted]
      linarith [directLdAccepted_add_rejected_eq_one D S types sample]]
    rw [_root_.LIDT.MIPStarRE.LDT.avgOver_sub, _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_const]
  rw [show _root_.MIPStarRE.QPBT.directLdRejectionProbability D S =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.LdType × _root_.MIPStarRE.QPBT.LdType))
        (fun types => 1 -
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectLdSpace D)) (accepted types)) by
    unfold _root_.MIPStarRE.QPBT.directLdRejectionProbability
    apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
    exact hbranch]
  rw [_root_.LIDT.MIPStarRE.LDT.avgOver_sub, _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_const]
  congr 1
  rw [_root_.MIPStarRE.QPBT.Strategy.value]
  symm
  change _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.directLdQuestionDistribution D)
      (fun xy : _root_.MIPStarRE.QPBT.DirectLdQuestion D × _root_.MIPStarRE.QPBT.DirectLdQuestion D =>
        ∑ a : (_root_.MIPStarRE.QPBT.directLdGame D).AnswerA, ∑ b : (_root_.MIPStarRE.QPBT.directLdGame D).AnswerB,
          if _root_.MIPStarRE.QPBT.directLdWinPredicate D xy.1 xy.2 a b then
            _root_.MIPStarRE.QPBT.outcomeWeight S xy.1 xy.2 a b else 0) = _
  rw [_root_.MIPStarRE.QPBT.directLdQuestionDistribution, _root_.LIDT.MIPStarRE.LDT.Distribution.avgOver_map]
  exact _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_prod (f := accepted)
