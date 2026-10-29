-- Prove2me | solution 1 for MIPStarRE.QPBT.MagicSquareRigidity.norm_alice_sub_bob_signObs_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:32:47.971482+00:00
-- url     : https://prove2.me/submissions/f33b2f74-da5b-413b-8815-6a9fb49fd6a6

-- Generated proof for MIPStarRE.QPBT.MagicSquareRigidity.norm_alice_sub_bob_signObs_sq_le.
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
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Reflections
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Relations
import Theorems.Thm_MIPStarRE_QPBT_MagicSquareRigidity_norm_apply_joint_defect_sq_le

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT.MagicSquareRigidity
end MIPStarRE.QPBT.MagicSquareRigidity
namespace MIPStarRE.QPBT.MagicSquareRigidity.NormCloseOn
end MIPStarRE.QPBT.MagicSquareRigidity.NormCloseOn

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

/-- The sign of a binary value is `1` or `-1`. -/
theorem bit_sign_eq_one_or_neg_one (b : ZMod 2) : _root_.MIPStarRE.QPBT.MagicSquareRigidity.bitSign b = 1 ∨ _root_.MIPStarRE.QPBT.MagicSquareRigidity.bitSign b = -1 := by
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) b with h | h <;> rw [h]
  · left
    norm_num [_root_.MIPStarRE.QPBT.MagicSquareRigidity.bitSign]
  · right
    norm_num [_root_.MIPStarRE.QPBT.MagicSquareRigidity.bitSign, ZMod.val_one]





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

/- Source helpers from QPBT/Test/MagicSquareTheorems/Rigidity/Reflections.lean. -/
/-!
# Reflections and the state-dependent metric on operators

The self-testing argument for the Magic Square game manipulates `±1`-valued
observables rather than positive operator valued measures.  This file records
the algebra of such observables and the estimates that convert Born masses into
operator bounds.

Postprocessing a projective measurement along a binary relabelling of its
answers produces a *reflection*, that is, a self-adjoint involution; two
reflections coming from one and the same measurement commute, and their product
is the reflection attached to the sum of the two relabellings.  The reflections
of the source are the binary observables of the rest of the development, so this
file uses `MIPStarRE.QPBT.IsBinaryObservable` and its algebra, defined in
`MIPStarRE/QPBT/Combining/Linearity/Defs.lean`, rather than a second predicate of
its own.  Two operators are compared through the norm of the difference of their
actions on a fixed state, the relation `NormCloseOn` below.  That relation is the
unsquared Euclidean distance between `M ψ` and `N ψ`; it is *not* the
state-dependent distance `≈_δ` of the source, which bounds the squared quantity
`⟨ψ|(M - N)ᴴ (M - N)|ψ⟩` and is formalized in this development by `opDistSq`.
The comparison is symmetric, satisfies the triangle inequality, and is unchanged
by multiplication on the left by an isometric operator; `NormCloseOn.opDistSq_le`
converts it into the source's relation.  Finally, a real spectral combination of
the joint effects of the two players has state-dependent norm controlled by the
Born mass of the answer pairs carrying a nonzero coefficient; this is the step
that turns each rejection mass of the value-to-parity layer into an operator
estimate.

## References

The statements supported here are the operator relations in `thm:ms-rigidity`,
blueprint `blueprint/src/chapter/ch13_qpbt_test.tex:224-253`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`,
proved in Coladangelo--Stark, arXiv:1709.09267v2, Theorem 6.9.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## Rectangular tensor placement -/

section Kron



/-- Formalization-only: scalars pass through the first factor. -/
theorem heteroKron_smul_left {ιA ιB : Type} (c : ℂ) (M : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (N : _root_.LIDT.MIPStarRE.Quantum.Op ιB) :
    _root_.MIPStarRE.QPBT.heteroKron (c • M) N = c • _root_.MIPStarRE.QPBT.heteroKron M N := by
  unfold _root_.MIPStarRE.QPBT.heteroKron
  exact Matrix.smul_kronecker c M N





end Kron

/-! ## The state-dependent norm -/



/-! ## Reflections

The *reflections* of `thm:ms-rigidity`, blueprint
`ch13_qpbt_test.tex:228-250`, are the self-adjoint involutions attached to
two-outcome projective measurements, which are exactly the binary observables
`MIPStarRE.QPBT.IsBinaryObservable` of
`MIPStarRE/QPBT/Combining/Linearity/Defs.lean`.  The Magic Square rigidity
argument therefore uses that predicate and its algebra directly:
`IsBinaryObservable.one`, `IsBinaryObservable.mul`,
`IsBinaryObservable.isometry`, `isBinaryObservable_heteroKron_one` and
`isBinaryObservable_one_heteroKron`. -/



/-! ## Closeness in the state-dependent norm -/





/-! ## Sign observables of a projective measurement -/



/-! ## Deviation of joint spectral combinations on the strategy state -/

section JointDefect

/-- Formalization-only: scalars pass through the second tensor factor. -/
theorem heteroKron_smul_right {ιA ιB : Type} (c : ℂ) (M : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (N : _root_.LIDT.MIPStarRE.Quantum.Op ιB) :
    _root_.MIPStarRE.QPBT.heteroKron M (c • N) = c • _root_.MIPStarRE.QPBT.heteroKron M N := by
  unfold _root_.MIPStarRE.QPBT.heteroKron
  exact Matrix.kronecker_smul c M N





variable {G : _root_.MIPStarRE.QPBT.Game}









/-- Formalization-only: expansion of a product of two local spectral
combinations into the joint effects. -/
theorem joint_expand (T : _root_.MIPStarRE.QPBT.Strategy G) (x : G.QuestionA) (y : G.QuestionB)
    (u : G.AnswerA → ℂ) (v : G.AnswerB → ℂ) :
    _root_.MIPStarRE.QPBT.heteroKron (∑ a, u a • (T.A x).effect a) (∑ b, v b • (T.B y).effect b) =
      ∑ a, ∑ b, (u a * v b) • _root_.MIPStarRE.QPBT.heteroKron ((T.A x).effect a) ((T.B y).effect b) := by
  rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.heteroKron_sum_left]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.heteroKron_smul_left, _root_.MIPStarRE.QPBT.MagicSquareRigidity.heteroKron_sum_right, Finset.smul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.heteroKron_smul_right, smul_smul]

/-- Formalization-only: the identity as a spectral combination of the effects of
a measurement. -/
theorem smul_one_eq_sum_smul_effect {α d : Type} [Fintype α] [Fintype d]
    [DecidableEq d] (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α d) (s : ℂ) :
    s • (1 : _root_.LIDT.MIPStarRE.Quantum.Op d) = ∑ a, s • M.effect a := by
  rw [← Finset.smul_sum, M.sum_eq_one]

end JointDefect

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

theorem solution (T : _root_.MIPStarRE.QPBT.Strategy G) (x : G.QuestionA)
    (y : G.QuestionB) (hA : _root_.MIPStarRE.QPBT.Measurement.IsProjective (T.A x))
    (hB : _root_.MIPStarRE.QPBT.Measurement.IsProjective (T.B y))
    (f : G.AnswerA → ZMod 2) (g : G.AnswerB → ZMod 2) :
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.MagicSquareRigidity.signObs (T.A x) f) 1 -
        _root_.MIPStarRE.QPBT.heteroKron 1 (_root_.MIPStarRE.QPBT.MagicSquareRigidity.signObs (T.B y) g)) T.ψ‖ ^ 2 ≤
      4 * _root_.MIPStarRE.QPBT.outcomeEventWeight T x y (fun a b => f a ≠ g b) := by
  classical
  have hAone : (1 : _root_.LIDT.MIPStarRE.Quantum.Op T.ιA) = ∑ a, (1 : ℂ) • (T.A x).effect a := by
    simpa using _root_.MIPStarRE.QPBT.MagicSquareRigidity.smul_one_eq_sum_smul_effect (T.A x) (1 : ℂ)
  have hBone : (1 : _root_.LIDT.MIPStarRE.Quantum.Op T.ιB) = ∑ b, (1 : ℂ) • (T.B y).effect b := by
    simpa using _root_.MIPStarRE.QPBT.MagicSquareRigidity.smul_one_eq_sum_smul_effect (T.B y) (1 : ℂ)
  have hexpand : _root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.MagicSquareRigidity.signObs (T.A x) f) 1 - _root_.MIPStarRE.QPBT.heteroKron 1 (_root_.MIPStarRE.QPBT.MagicSquareRigidity.signObs (T.B y) g) =
      ∑ a, ∑ b, ((_root_.MIPStarRE.QPBT.MagicSquareRigidity.bitSign (f a) - _root_.MIPStarRE.QPBT.MagicSquareRigidity.bitSign (g b) : ℝ) : ℂ) •
        _root_.MIPStarRE.QPBT.heteroKron ((T.A x).effect a) ((T.B y).effect b) := by
    rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.signObs, _root_.MIPStarRE.QPBT.MagicSquareRigidity.signObs]
    nth_rewrite 1 [hBone]
    nth_rewrite 1 [hAone]
    rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.joint_expand, _root_.MIPStarRE.QPBT.MagicSquareRigidity.joint_expand, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← sub_smul]
    congr 1
    push_cast
    ring
  rw [hexpand]
  refine _root_.MIPStarRE.QPBT.MagicSquareRigidity.norm_apply_joint_defect_sq_le T x y hA hB
    (fun a b => _root_.MIPStarRE.QPBT.MagicSquareRigidity.bitSign (f a) - _root_.MIPStarRE.QPBT.MagicSquareRigidity.bitSign (g b)) (fun a b => f a ≠ g b) ?_ ?_
  · intro a b
    rcases _root_.MIPStarRE.QPBT.MagicSquareRigidity.bit_sign_eq_one_or_neg_one (f a) with h1 | h1 <;>
      rcases _root_.MIPStarRE.QPBT.MagicSquareRigidity.bit_sign_eq_one_or_neg_one (g b) with h2 | h2 <;>
        simp only [h1, h2] <;> norm_num
  · intro a b hab
    rw [not_not] at hab
    rw [hab, sub_self]
