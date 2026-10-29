-- Prove2me | solution 1 for MIPStarRE.QPBT.sum_outcome_weight_right
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:28:35.58133+00:00
-- url     : https://prove2.me/submissions/be918aed-afb8-41f4-8c98-05069ea2b770

-- Generated proof for MIPStarRE.QPBT.sum_outcome_weight_right.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Games_Defs

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

theorem solution {G : _root_.MIPStarRE.QPBT.Game} (S : _root_.MIPStarRE.QPBT.Strategy G)
    (x : G.QuestionA) (y : G.QuestionB) (a : G.AnswerA) :
    (∑ b : G.AnswerB, _root_.MIPStarRE.QPBT.outcomeWeight S x y a b) = _root_.MIPStarRE.QPBT.aliceOutcomeWeight S x a := by
  have hsum :
      (∑ b : G.AnswerB, _root_.MIPStarRE.QPBT.heteroKron ((S.A x).effect a) ((S.B y).effect b)) =
        _root_.MIPStarRE.QPBT.heteroKron ((S.A x).effect a) 1 := by
    ext i j
    simp only [Matrix.sum_apply, _root_.MIPStarRE.QPBT.heteroKron, Matrix.kronecker,
      Matrix.kroneckerMap_apply]
    rw [← Finset.mul_sum]
    rw [show (∑ b : G.AnswerB, (S.B y).effect b i.2 j.2) =
        (1 : _root_.LIDT.MIPStarRE.Quantum.Op S.ιB) i.2 j.2 by
      simpa only [Matrix.sum_apply] using congrFun (congrFun (S.B y).sum_eq_one i.2) j.2]
  calc
    (∑ b : G.AnswerB, _root_.MIPStarRE.QPBT.outcomeWeight S x y a b) =
        (inner ℂ S.ψ
          (_root_.MIPStarRE.QPBT.applyOperatorToState
            (∑ b : G.AnswerB,
              _root_.MIPStarRE.QPBT.heteroKron ((S.A x).effect a) ((S.B y).effect b)) S.ψ)).re := by
          simp [_root_.MIPStarRE.QPBT.outcomeWeight, _root_.MIPStarRE.QPBT.applyOperatorToState]
    _ = (inner ℂ S.ψ
        (_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron ((S.A x).effect a) 1) S.ψ)).re := by
      rw [hsum]
    _ = _root_.MIPStarRE.QPBT.aliceOutcomeWeight S x a := rfl
