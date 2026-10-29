-- Prove2me | solution 1 for MIPStarRE.QPBT.MagicSquareRigidity.msVarObsA_anticommute
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:53:52.691872+00:00
-- url     : https://prove2.me/submissions/1ac70a08-24de-48eb-a59f-2cf727b62342

-- Generated proof for MIPStarRE.QPBT.MagicSquareRigidity.msVarObsA_anticommute.
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
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Test_MagicSquare
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_CellRelations
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Dilation
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_GroundSlice
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Reflections
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Relations
import Theorems.Thm_MIPStarRE_QPBT_MagicSquareRigidity_msCellObsB_mul_close
import Theorems.Thm_MIPStarRE_QPBT_MagicSquareRigidity_msCellObsB_mul_close_of_same_cells
import Theorems.Thm_MIPStarRE_QPBT_MagicSquareRigidity_msCellObsB_step

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT.MagicSquareRigidity
end MIPStarRE.QPBT.MagicSquareRigidity
namespace MIPStarRE.QPBT.MagicSquareRigidity.NormCloseOn
end MIPStarRE.QPBT.MagicSquareRigidity.NormCloseOn

/- Source helpers from QPBT/Test/MagicSquareTheorems/Rigidity/Anticommutation.lean. -/
/-!
# Approximate anticommutation in the Magic Square game

The Magic Square is the smallest linear constraint system whose solution group
forces two of its generators to anticommute.  This file carries out that
computation on the projective dilation of an arbitrary strategy, in the
state-dependent norm and with explicit constants.

The computation proceeds in three identical steps.  Each step takes two
constraints sharing exactly one cell and rewrites a product of two cell
reflections, one from each constraint, as the signed product of the two
reflections at the remaining cells.  Iterating the step around the grid returns
to the pair one started from, in the opposite order and with the sign reversed
by the exceptional parity of the third column; this yields the approximate
anticommutation of the two reflections at the cells labelled by the paper's
first and fifth variables.

The final squared-distance corollaries measure the anticommutation defects of
the dilated strategy on its own state, in the `opDistSq` convention of
`def:povm-distance`, at the scale `624 ^ 2 * sqrt ε`.  These are pre-isometry
estimates.  The post-isometry estimates on the ideal EPR-pair-plus-auxiliary
state in `thm:ms-rigidity` are obtained from them through
`ms_anticommutator_transfer_A` and `ms_anticommutator_transfer_B` in the
swap-isometry packet, issue Dengnifer/MIPStarRE-QPBT-bak#104.

## References

The statement supported here is `thm:ms-rigidity` in
`blueprint/src/chapter/ch13_qpbt_test.tex:224-253`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`,
proved in Coladangelo--Stark, arXiv:1709.09267v2, Theorem 6.9; the argument
below is the Magic Square instance of the solution-group computation used there
(their Figure describing the generators of the solution group).  The variable
and constraint indices are zero-based, so the paper's first and fifth variables
are the cells `0` and `4`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## Placement of an operator on one player's tensor factor -/

























/-! ## Isometry bookkeeping -/







/-! ## One step of the solution-group computation -/



/-! ## Negation and the sign of a constraint -/

/-- Formalization-only: closeness to a negation is symmetric in the two
operators, because `M - (-N) = N - (-M)`.  Used by the solution-group
computations of both logical Pauli pairs. -/
theorem normCloseOn_neg_swap {ι : Type} [Fintype ι] [DecidableEq ι]
    {ψ : EuclideanSpace ℂ ι} {δ : ℝ} {M N : _root_.LIDT.MIPStarRE.Quantum.Op ι} (h : _root_.MIPStarRE.QPBT.MagicSquareRigidity.NormCloseOn ψ δ M (-N)) :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.NormCloseOn ψ δ N (-M) := by
  change ‖_root_.MIPStarRE.QPBT.applyOperatorToState (N - -M) ψ‖ ≤ δ
  rw [show N - -M = M - -N by abel]
  exact h

/-! ## The Magic Square instance of one step -/





/-! ## Approximate anticommutation of the two logical Pauli pairs -/





/-! ## The computation on Alice's cell reflections -/















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



namespace NormCloseOn

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {ψ : EuclideanSpace ℂ ι} {δ η : ℝ} {M N P U : _root_.LIDT.MIPStarRE.Quantum.Op ι}



/-- Closeness is symmetric. -/
theorem symm (h : _root_.MIPStarRE.QPBT.MagicSquareRigidity.NormCloseOn ψ δ M N) : _root_.MIPStarRE.QPBT.MagicSquareRigidity.NormCloseOn ψ δ N M := by
  have happ : _root_.MIPStarRE.QPBT.applyOperatorToState (N - M) ψ = -_root_.MIPStarRE.QPBT.applyOperatorToState (M - N) ψ := by
    rw [show N - M = -(M - N) by abel]
    unfold _root_.MIPStarRE.QPBT.applyOperatorToState
    simp only [map_neg, LinearMap.neg_apply]
  rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.NormCloseOn, happ, norm_neg]
  exact h

/-- Enlarging the scale preserves closeness. -/
theorem mono (h : _root_.MIPStarRE.QPBT.MagicSquareRigidity.NormCloseOn ψ δ M N) (hδ : δ ≤ η) : _root_.MIPStarRE.QPBT.MagicSquareRigidity.NormCloseOn ψ η M N :=
  le_trans h hδ

/-- Closeness composes by the triangle inequality. -/
theorem trans (h₁ : _root_.MIPStarRE.QPBT.MagicSquareRigidity.NormCloseOn ψ δ M N) (h₂ : _root_.MIPStarRE.QPBT.MagicSquareRigidity.NormCloseOn ψ η N P) :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.NormCloseOn ψ (δ + η) M P := by
  have hsplit : M - P = (M - N) + (N - P) := by abel
  calc ‖_root_.MIPStarRE.QPBT.applyOperatorToState (M - P) ψ‖
      = ‖_root_.MIPStarRE.QPBT.applyOperatorToState (M - N) ψ + _root_.MIPStarRE.QPBT.applyOperatorToState (N - P) ψ‖ := by
        rw [hsplit, _root_.MIPStarRE.QPBT.MagicSquareRigidity.applyOperatorToState_add_op]
    _ ≤ ‖_root_.MIPStarRE.QPBT.applyOperatorToState (M - N) ψ‖ + ‖_root_.MIPStarRE.QPBT.applyOperatorToState (N - P) ψ‖ :=
        norm_add_le _ _
    _ ≤ δ + η := add_le_add h₁ h₂



/-- Negating both operators leaves the state-dependent norm of the difference
unchanged. -/
theorem neg (h : _root_.MIPStarRE.QPBT.MagicSquareRigidity.NormCloseOn ψ δ M N) : _root_.MIPStarRE.QPBT.MagicSquareRigidity.NormCloseOn ψ δ (-M) (-N) := by
  change ‖_root_.MIPStarRE.QPBT.applyOperatorToState (-M - -N) ψ‖ ≤ δ
  rw [show -M - -N = -(M - N) by abel]
  have happ : _root_.MIPStarRE.QPBT.applyOperatorToState (-(M - N)) ψ =
      -_root_.MIPStarRE.QPBT.applyOperatorToState (M - N) ψ := by
    unfold _root_.MIPStarRE.QPBT.applyOperatorToState
    simp only [map_neg, LinearMap.neg_apply]
  rw [happ, norm_neg]
  exact h







end NormCloseOn

/-! ## Sign observables of a projective measurement -/



/-! ## Deviation of joint spectral combinations on the strategy state -/



end

end MIPStarRE.QPBT.MagicSquareRigidity

/-!
# Approximate anticommutation in the Magic Square game

The Magic Square is the smallest linear constraint system whose solution group
forces two of its generators to anticommute.  This file carries out that
computation on the projective dilation of an arbitrary strategy, in the
state-dependent norm and with explicit constants.

The computation proceeds in three identical steps.  Each step takes two
constraints sharing exactly one cell and rewrites a product of two cell
reflections, one from each constraint, as the signed product of the two
reflections at the remaining cells.  Iterating the step around the grid returns
to the pair one started from, in the opposite order and with the sign reversed
by the exceptional parity of the third column; this yields the approximate
anticommutation of the two reflections at the cells labelled by the paper's
first and fifth variables.

The final squared-distance corollaries measure the anticommutation defects of
the dilated strategy on its own state, in the `opDistSq` convention of
`def:povm-distance`, at the scale `624 ^ 2 * sqrt ε`.  These are pre-isometry
estimates.  The post-isometry estimates on the ideal EPR-pair-plus-auxiliary
state in `thm:ms-rigidity` are obtained from them through
`ms_anticommutator_transfer_A` and `ms_anticommutator_transfer_B` in the
swap-isometry packet, issue Dengnifer/MIPStarRE-QPBT-bak#104.

## References

The statement supported here is `thm:ms-rigidity` in
`blueprint/src/chapter/ch13_qpbt_test.tex:224-253`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`,
proved in Coladangelo--Stark, arXiv:1709.09267v2, Theorem 6.9; the argument
below is the Magic Square instance of the solution-group computation used there
(their Figure describing the generators of the solution group).  The variable
and constraint indices are zero-based, so the paper's first and fifth variables
are the cells `0` and `4`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT.MagicSquareRigidity

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum



/-! ## Placement of an operator on one player's tensor factor -/

























/-! ## Isometry bookkeeping -/







/-! ## One step of the solution-group computation -/



/-! ## Negation and the sign of a constraint -/



/-! ## The Magic Square instance of one step -/





/-! ## Approximate anticommutation of the two logical Pauli pairs -/

theorem solution (S : _root_.MIPStarRE.QPBT.Strategy _root_.MIPStarRE.QPBT.msGame) (ε : ℝ) (hwin : 1 - ε ≤ S.value) :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.NormCloseOn (_root_.MIPStarRE.QPBT.MagicSquareRigidity.msDilatedStrategy S).ψ (624 * Real.sqrt ε)
      (_root_.MIPStarRE.QPBT.MagicSquareRigidity.msVarObsA S 0 * _root_.MIPStarRE.QPBT.MagicSquareRigidity.msVarObsA S 4) (-(_root_.MIPStarRE.QPBT.MagicSquareRigidity.msVarObsA S 4 * _root_.MIPStarRE.QPBT.MagicSquareRigidity.msVarObsA S 0)) := by
  have hA : ∀ a : _root_.MIPStarRE.QPBT.MsAnswer, _root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitOrZero 1 a + _root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitOrZero 0 a +
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitOrZero 2 a = _root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitSum a := by
    intro a; simp only [_root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitSum]; ring
  have hA' : ∀ a : _root_.MIPStarRE.QPBT.MsAnswer, _root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitOrZero 0 a + _root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitOrZero 1 a +
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitOrZero 2 a = _root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitSum a := fun a => rfl
  have hB : ∀ a : _root_.MIPStarRE.QPBT.MsAnswer, _root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitOrZero 2 a + _root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitOrZero 0 a +
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitOrZero 1 a = _root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitSum a := by
    intro a; simp only [_root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitSum]; ring
  have hB' : ∀ a : _root_.MIPStarRE.QPBT.MsAnswer, _root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitOrZero 2 a + _root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitOrZero 1 a +
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitOrZero 0 a = _root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitSum a := by
    intro a; simp only [_root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitSum]; ring
  have hC : ∀ a : _root_.MIPStarRE.QPBT.MsAnswer, _root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitOrZero 0 a + _root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitOrZero 2 a +
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitOrZero 1 a = _root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitSum a := by
    intro a; simp only [_root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitSum]; ring
  have hC' : ∀ a : _root_.MIPStarRE.QPBT.MsAnswer, _root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitOrZero 1 a + _root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitOrZero 2 a +
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitOrZero 0 a = _root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitSum a := by
    intro a; simp only [_root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitSum]; ring
  have hsign_pos : ∀ i : Fin 6, i ≠ 5 →
      ((_root_.MIPStarRE.QPBT.MagicSquareRigidity.bitSign (_root_.MIPStarRE.QPBT.msParity i) : ℝ) : ℂ) = 1 := by
    intro i hi
    have hp : _root_.MIPStarRE.QPBT.msParity i = 0 := by
      unfold _root_.MIPStarRE.QPBT.msParity
      rw [if_neg]
      intro hv
      exact hi (Fin.ext hv)
    rw [hp]
    norm_num [_root_.MIPStarRE.QPBT.MagicSquareRigidity.bitSign]
  have hsign_neg : ((_root_.MIPStarRE.QPBT.MagicSquareRigidity.bitSign (_root_.MIPStarRE.QPBT.msParity 5) : ℝ) : ℂ) = -1 := by
    have hp : _root_.MIPStarRE.QPBT.msParity 5 = 1 := by norm_num [_root_.MIPStarRE.QPBT.msParity]
    rw [hp]
    norm_num [_root_.MIPStarRE.QPBT.MagicSquareRigidity.bitSign, ZMod.val_one]
  -- the three steps of the computation
  have stepA := _root_.MIPStarRE.QPBT.MagicSquareRigidity.msCellObsB_step S ε hwin 0 4 1 0 2 0 1 2 hA hA' (by decide)
  rw [hsign_pos 0 (by decide), hsign_pos 4 (by decide), one_mul, one_smul] at stepA
  have stepB := _root_.MIPStarRE.QPBT.MagicSquareRigidity.msCellObsB_step S ε hwin 5 2 2 0 1 2 1 0 hB hB' (by decide)
  rw [hsign_neg, hsign_pos 2 (by decide), mul_one, neg_one_smul] at stepB
  have stepC := _root_.MIPStarRE.QPBT.MagicSquareRigidity.msCellObsB_step S ε hwin 1 3 0 2 1 1 2 0 hC hC' (by decide)
  rw [hsign_pos 1 (by decide), hsign_pos 3 (by decide), one_mul, one_smul] at stepC
  -- the three changes of representative
  have linkA := _root_.MIPStarRE.QPBT.MagicSquareRigidity.msCellObsB_mul_close_of_same_cells S ε hwin 0 4 5 2 2 2 0 1
    (by decide) (by decide)
  have linkB := _root_.MIPStarRE.QPBT.MagicSquareRigidity.msCellObsB_mul_close_of_same_cells S ε hwin 5 2 1 3 1 0 2 2
    (by decide) (by decide)
  have linkC := _root_.MIPStarRE.QPBT.MagicSquareRigidity.msCellObsB_mul_close_of_same_cells S ε hwin 1 3 4 0 1 0 1 0
    (by decide) (by decide)
  -- passage between Alice's variable reflections and Bob's cell reflections
  have hstart := (_root_.MIPStarRE.QPBT.MagicSquareRigidity.msCellObsB_mul_close S ε hwin 0 4 0 1).symm
  have hend := _root_.MIPStarRE.QPBT.MagicSquareRigidity.msCellObsB_mul_close S ε hwin 4 0 1 0
  rw [show _root_.MIPStarRE.QPBT.msConstraintVars 4 1 = 4 from by decide,
    show _root_.MIPStarRE.QPBT.msConstraintVars 0 0 = 0 from by decide] at hstart hend
  have hchain := ((((((hstart.trans stepA).trans linkA).trans stepB).trans
    linkB.neg).trans stepC.neg).trans linkC.neg).trans hend.neg
  exact _root_.MIPStarRE.QPBT.MagicSquareRigidity.normCloseOn_neg_swap (hchain.mono (by linarith))
