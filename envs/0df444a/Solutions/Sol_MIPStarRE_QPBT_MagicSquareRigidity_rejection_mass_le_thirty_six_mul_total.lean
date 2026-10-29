-- Prove2me | solution 1 for MIPStarRE.QPBT.MagicSquareRigidity.rejection_mass_le_thirty_six_mul_total
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:37:43.765705+00:00
-- url     : https://prove2.me/submissions/faf2cf0c-6c24-41a5-becf-7ab3a5a8757f

-- Generated proof for MIPStarRE.QPBT.MagicSquareRigidity.rejection_mass_le_thirty_six_mul_total.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
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
import Definitions.Def_QPBT_QPBT_Games_CondLinear
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Test_MagicSquare
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Relations
import Theorems.Thm_MIPStarRE_QPBT_MagicSquareRigidity_ms_question_weight_ge

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.MagicSquareRigidity
end MIPStarRE.QPBT.MagicSquareRigidity

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

/- Source helpers from QPBT/Test/MagicSquareTheorems/Rigidity/Relations.lean. -/
/-!
# Magic Square value-to-parity relations

This file extracts the elementary probability relations used at the start of
the Magic Square rigidity argument.  A strategy of value at least `1 - ε` has
total rejection mass at most `ε`.  Since the question distribution is
supported on at most 36 directed incidences, the rejection mass at each
incidence is at most `36 * ε`.  This controls malformed answers, consistency
of the two reported bits at every cell, and the parity product on each of the
six row or column constraints.

The arguments apply to arbitrary finite POVMs.  In particular, malformed
answers remain in the event masses when `msBitOrZero` and
`constraintBitOrZero` turn the common answer alphabet into binary outcomes.

## References

The Magic Square game is defined in
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:512-610`
and blueprint `def:ms-game`.  These relations are the
probabilistic input to the rigidity result cited at paper lines 612-652 from
Coladangelo--Stark, Theorem 6.9.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## The directed incidence distribution -/













/-! ## Rejection mass from the game value -/





















/-- Conditioned rejection mass is nonnegative. -/
theorem rejection_mass_nonneg (S : _root_.MIPStarRE.QPBT.Strategy _root_.MIPStarRE.QPBT.msGame) (x y : _root_.MIPStarRE.QPBT.MsType) :
    0 ≤ _root_.MIPStarRE.QPBT.MagicSquareRigidity.rejectionMass S x y :=
  _root_.MIPStarRE.QPBT.outcome_event_weight_nonneg S x y fun a b => _root_.MIPStarRE.QPBT.msWinPredicate x y a b = false







/-! ## Malformed answers and cell consistency -/























































/-! ## Row and column parity products -/





































end

end MIPStarRE.QPBT.MagicSquareRigidity

/-!
# Magic Square value-to-parity relations

This file extracts the elementary probability relations used at the start of
the Magic Square rigidity argument.  A strategy of value at least `1 - ε` has
total rejection mass at most `ε`.  Since the question distribution is
supported on at most 36 directed incidences, the rejection mass at each
incidence is at most `36 * ε`.  This controls malformed answers, consistency
of the two reported bits at every cell, and the parity product on each of the
six row or column constraints.

The arguments apply to arbitrary finite POVMs.  In particular, malformed
answers remain in the event masses when `msBitOrZero` and
`constraintBitOrZero` turn the common answer alphabet into binary outcomes.

## References

The Magic Square game is defined in
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:512-610`
and blueprint `def:ms-game`.  These relations are the
probabilistic input to the rigidity result cited at paper lines 612-652 from
Coladangelo--Stark, Theorem 6.9.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT.MagicSquareRigidity

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum



/-! ## The directed incidence distribution -/













/-! ## Rejection mass from the game value -/

theorem solution (S : _root_.MIPStarRE.QPBT.Strategy _root_.MIPStarRE.QPBT.msGame)
    {xy : _root_.MIPStarRE.QPBT.MsType × _root_.MIPStarRE.QPBT.MsType}
    (hxy : xy ∈ (_root_.MIPStarRE.QPBT.graphDistribution _root_.MIPStarRE.QPBT.msEdges _root_.MIPStarRE.QPBT.msEdges_nonempty).support) :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.rejectionMass S xy.1 xy.2 ≤ 36 * _root_.MIPStarRE.QPBT.MagicSquareRigidity.totalRejectionMass S := by
  have hrejection : 0 ≤ _root_.MIPStarRE.QPBT.MagicSquareRigidity.rejectionMass S xy.1 xy.2 :=
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.rejection_mass_nonneg S xy.1 xy.2
  have hweight := _root_.MIPStarRE.QPBT.MagicSquareRigidity.ms_question_weight_ge hxy
  have hterm :
      (_root_.MIPStarRE.QPBT.graphDistribution _root_.MIPStarRE.QPBT.msEdges _root_.MIPStarRE.QPBT.msEdges_nonempty).weight xy *
          _root_.MIPStarRE.QPBT.MagicSquareRigidity.rejectionMass S xy.1 xy.2 ≤ _root_.MIPStarRE.QPBT.MagicSquareRigidity.totalRejectionMass S := by
    unfold _root_.MIPStarRE.QPBT.MagicSquareRigidity.totalRejectionMass _root_.LIDT.MIPStarRE.LDT.avgOver
    exact Finset.single_le_sum
      (fun z _ => mul_nonneg
        ((_root_.MIPStarRE.QPBT.graphDistribution _root_.MIPStarRE.QPBT.msEdges _root_.MIPStarRE.QPBT.msEdges_nonempty).nonnegative z)
        (_root_.MIPStarRE.QPBT.MagicSquareRigidity.rejection_mass_nonneg S z.1 z.2)) hxy
  have hscaled : (1 / 36 : ℝ) * _root_.MIPStarRE.QPBT.MagicSquareRigidity.rejectionMass S xy.1 xy.2 ≤
      (_root_.MIPStarRE.QPBT.graphDistribution _root_.MIPStarRE.QPBT.msEdges _root_.MIPStarRE.QPBT.msEdges_nonempty).weight xy *
        _root_.MIPStarRE.QPBT.MagicSquareRigidity.rejectionMass S xy.1 xy.2 :=
    mul_le_mul_of_nonneg_right hweight hrejection
  nlinarith
