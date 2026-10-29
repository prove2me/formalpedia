-- Prove2me | solution 1 for MIPStarRE.QPBT.MagicSquareRigidity.constraintParityFailure_of_bitSum_ne
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:08:26.757963+00:00
-- url     : https://prove2.me/submissions/f796deb8-2b4e-4736-ba2e-c5184fc78628

-- Generated proof for MIPStarRE.QPBT.MagicSquareRigidity.constraintParityFailure_of_bitSum_ne.
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
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Test_MagicSquare
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_CellRelations
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Relations

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT.MagicSquareRigidity
end MIPStarRE.QPBT.MagicSquareRigidity

/- Source helpers from QPBT/Test/MagicSquareTheorems/Rigidity/CellRelations.lean. -/
/-!
# The Magic Square cell relations on the dilated strategy

Every question of the projectively dilated Magic Square strategy carries a
complete projective measurement, so each binary relabelling of its answers
produces a reflection.  Three reflections are attached to a constraint question,
one for each cell of the row or column, and one reflection is attached to each
variable question; the three reflections of a constraint commute exactly and
their product, in any order, is the reflection of the sum of the three reported
bits.  Reflections of the two players commute exactly.

The value-to-parity relations are converted here into operator estimates on the
dilated state, with explicit constants: the six row and column products are
close to the sign prescribed by the corresponding linear equation, and the two
reflections that the two players attach to a common cell are close to each
other.  The two logical Pauli pairs are the reflections at the cells labelled by
the paper's first and fifth variables.

## References

The statement supported here is `thm:ms-rigidity` in
`blueprint/src/chapter/ch13_qpbt_test.tex:224-253`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`,
proved in Coladangelo--Stark, arXiv:1709.09267v2, Theorem 6.9.  The variable and
constraint indices are zero-based, so the paper's first and fifth variables are
the cells `0` and `4`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## Deviation of a sign observable from a comparison observable -/



/-- The sign is injective on binary values. -/
theorem bit_sign_injective : Function.Injective _root_.MIPStarRE.QPBT.MagicSquareRigidity.bitSign := by
  intro b c hbc
  by_contra hne
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) b with hb | hb <;>
    rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) c with hc | hc
  · exact hne (hb.trans hc.symm)
  · rw [hb, hc] at hbc
    norm_num [_root_.MIPStarRE.QPBT.MagicSquareRigidity.bitSign, ZMod.val_one] at hbc
  · rw [hb, hc] at hbc
    norm_num [_root_.MIPStarRE.QPBT.MagicSquareRigidity.bitSign, ZMod.val_one] at hbc
  · exact hne (hb.trans hc.symm)



/-! ## Comparison of Born masses with the game error -/







/-! ## The Magic Square reflections of the dilated strategy -/

































/-! ## The six row and column product relations -/

















/-! ## Agreement of the two reflections attached to a common cell -/





/-! ## Permuted row and column products -/









/-! ## The two logical Pauli pairs -/

























/-! ## Unit scalars -/







/-! ## Building blocks of the solution-group computation -/







end

end MIPStarRE.QPBT.MagicSquareRigidity

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





























/-! ## Malformed answers and cell consistency -/























































/-! ## Row and column parity products -/



/-- The binary sign turns addition into multiplication. -/
theorem bit_sign_add (b c : ZMod 2) :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.bitSign (b + c) = _root_.MIPStarRE.QPBT.MagicSquareRigidity.bitSign b * _root_.MIPStarRE.QPBT.MagicSquareRigidity.bitSign c := by
  unfold _root_.MIPStarRE.QPBT.MagicSquareRigidity.bitSign
  rw [ZMod.val_add]
  rw [← neg_one_pow_eq_pow_mod_two]
  exact pow_add _ _ _

/-- The sign of a three-bit parity is the product of the three signs. -/
theorem bit_sign_sum_fin_three (β : Fin 3 → ZMod 2) :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.bitSign (∑ k : Fin 3, β k) = ∏ k : Fin 3, _root_.MIPStarRE.QPBT.MagicSquareRigidity.bitSign (β k) := by
  rw [Fin.sum_univ_three, Fin.prod_univ_three, _root_.MIPStarRE.QPBT.MagicSquareRigidity.bit_sign_add, _root_.MIPStarRE.QPBT.MagicSquareRigidity.bit_sign_add]

/-- A binary sign is never zero. -/
theorem bit_sign_ne_zero (b : ZMod 2) : _root_.MIPStarRE.QPBT.MagicSquareRigidity.bitSign b ≠ 0 := by
  unfold _root_.MIPStarRE.QPBT.MagicSquareRigidity.bitSign
  exact pow_ne_zero _ (by norm_num)











/-- Every wrong-form constraint answer is included in the parity-failure event. -/
theorem wrong_constraint_answer_implies_parity_failure (i : Fin 6) (a : _root_.MIPStarRE.QPBT.MsAnswer)
    (ha : _root_.MIPStarRE.QPBT.MagicSquareRigidity.wrongConstraintAnswer a = true) : _root_.MIPStarRE.QPBT.MagicSquareRigidity.ConstraintParityFailure i a := by
  cases a with
  | triple β => simp [_root_.MIPStarRE.QPBT.MagicSquareRigidity.wrongConstraintAnswer] at ha
  | bit γ =>
      unfold _root_.MIPStarRE.QPBT.MagicSquareRigidity.ConstraintParityFailure _root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintParityProduct
      exact (_root_.MIPStarRE.QPBT.MagicSquareRigidity.bit_sign_ne_zero (_root_.MIPStarRE.QPBT.msParity i)).symm

















end

end MIPStarRE.QPBT.MagicSquareRigidity

/-!
# The Magic Square cell relations on the dilated strategy

Every question of the projectively dilated Magic Square strategy carries a
complete projective measurement, so each binary relabelling of its answers
produces a reflection.  Three reflections are attached to a constraint question,
one for each cell of the row or column, and one reflection is attached to each
variable question; the three reflections of a constraint commute exactly and
their product, in any order, is the reflection of the sum of the three reported
bits.  Reflections of the two players commute exactly.

The value-to-parity relations are converted here into operator estimates on the
dilated state, with explicit constants: the six row and column products are
close to the sign prescribed by the corresponding linear equation, and the two
reflections that the two players attach to a common cell are close to each
other.  The two logical Pauli pairs are the reflections at the cells labelled by
the paper's first and fifth variables.

## References

The statement supported here is `thm:ms-rigidity` in
`blueprint/src/chapter/ch13_qpbt_test.tex:224-253`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`,
proved in Coladangelo--Stark, arXiv:1709.09267v2, Theorem 6.9.  The variable and
constraint indices are zero-based, so the paper's first and fifth variables are
the cells `0` and `4`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT.MagicSquareRigidity

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum



/-! ## Deviation of a sign observable from a comparison observable -/







variable {G : _root_.MIPStarRE.QPBT.Game}









/-! ## Comparison of Born masses with the game error -/







/-! ## The Magic Square reflections of the dilated strategy -/

































/-! ## The six row and column product relations -/

theorem solution (i : Fin 6) (a : _root_.MIPStarRE.QPBT.MsAnswer)
    (h : _root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitSum a ≠ _root_.MIPStarRE.QPBT.msParity i) : _root_.MIPStarRE.QPBT.MagicSquareRigidity.ConstraintParityFailure i a := by
  cases a with
  | bit γ => exact _root_.MIPStarRE.QPBT.MagicSquareRigidity.wrong_constraint_answer_implies_parity_failure i (_root_.MIPStarRE.QPBT.MsAnswer.bit γ) rfl
  | triple β =>
      intro hprod
      apply h
      have hsum : _root_.MIPStarRE.QPBT.MagicSquareRigidity.bitSign (∑ k : Fin 3, β k) = _root_.MIPStarRE.QPBT.MagicSquareRigidity.bitSign (_root_.MIPStarRE.QPBT.msParity i) := by
        rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.bit_sign_sum_fin_three]
        exact hprod
      have hbit := _root_.MIPStarRE.QPBT.MagicSquareRigidity.bit_sign_injective hsum
      rw [Fin.sum_univ_three] at hbit
      exact hbit
