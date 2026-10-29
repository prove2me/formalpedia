-- Prove2me | solution 1 for MIPStarRE.QPBT.rejectionMass_eq_one_sub_value
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:32:14.524273+00:00
-- url     : https://prove2.me/submissions/c9755d17-b94a-4f6f-a5cd-5ee7874c8cbf

-- Generated proof for MIPStarRE.QPBT.rejectionMass_eq_one_sub_value.
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
import Definitions.Def_QPBT_QPBT_Games_Defs
import Theorems.Thm_MIPStarRE_QPBT_outcomeWeight_sum_eq_one

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

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



open scoped BigOperators Matrix ComplexOrder

open MIPStarRE.QPBT

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

theorem solution {G : _root_.MIPStarRE.QPBT.Game} (S : _root_.MIPStarRE.QPBT.Strategy G) :
    _root_.LIDT.MIPStarRE.LDT.avgOver G.μ (fun questions =>
      ∑ a, ∑ b,
        if G.decide questions.1 questions.2 a b then 0
        else _root_.MIPStarRE.QPBT.outcomeWeight S questions.1 questions.2 a b) =
      1 - S.value := by
  classical
  rw [show _root_.LIDT.MIPStarRE.LDT.avgOver G.μ (fun questions =>
      ∑ a, ∑ b,
        if G.decide questions.1 questions.2 a b then 0
        else _root_.MIPStarRE.QPBT.outcomeWeight S questions.1 questions.2 a b) =
      _root_.LIDT.MIPStarRE.LDT.avgOver G.μ (fun questions =>
        1 - ∑ a, ∑ b,
          if G.decide questions.1 questions.2 a b then
            _root_.MIPStarRE.QPBT.outcomeWeight S questions.1 questions.2 a b else 0) by
    apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
    intro questions
    calc
      (∑ a, ∑ b,
          if G.decide questions.1 questions.2 a b then 0
          else _root_.MIPStarRE.QPBT.outcomeWeight S questions.1 questions.2 a b) =
          ∑ a, ∑ b,
            (_root_.MIPStarRE.QPBT.outcomeWeight S questions.1 questions.2 a b -
              if G.decide questions.1 questions.2 a b then
                _root_.MIPStarRE.QPBT.outcomeWeight S questions.1 questions.2 a b else 0) := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        split <;> simp
      _ = (∑ a, ∑ b, _root_.MIPStarRE.QPBT.outcomeWeight S questions.1 questions.2 a b) -
          ∑ a, ∑ b,
            if G.decide questions.1 questions.2 a b then
              _root_.MIPStarRE.QPBT.outcomeWeight S questions.1 questions.2 a b else 0 := by
        rw [show (∑ a, ∑ b,
            (_root_.MIPStarRE.QPBT.outcomeWeight S questions.1 questions.2 a b -
              if G.decide questions.1 questions.2 a b then
                _root_.MIPStarRE.QPBT.outcomeWeight S questions.1 questions.2 a b else 0)) =
            ∑ a, ((∑ b, _root_.MIPStarRE.QPBT.outcomeWeight S questions.1 questions.2 a b) -
              ∑ b, if G.decide questions.1 questions.2 a b then
                _root_.MIPStarRE.QPBT.outcomeWeight S questions.1 questions.2 a b else 0) by
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.sum_sub_distrib]]
        rw [Finset.sum_sub_distrib]
      _ = 1 - ∑ a, ∑ b,
          if G.decide questions.1 questions.2 a b then
            _root_.MIPStarRE.QPBT.outcomeWeight S questions.1 questions.2 a b else 0 := by
        rw [_root_.MIPStarRE.QPBT.outcomeWeight_sum_eq_one]]
  rw [_root_.LIDT.MIPStarRE.LDT.avgOver_sub, _root_.LIDT.MIPStarRE.LDT.avgOver_const_of_isProbability G.μ G.μ_prob]
  rfl
