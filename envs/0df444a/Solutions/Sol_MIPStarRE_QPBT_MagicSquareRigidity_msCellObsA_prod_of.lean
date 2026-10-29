-- Prove2me | solution 1 for MIPStarRE.QPBT.MagicSquareRigidity.msCellObsA_prod_of
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:23:39.240541+00:00
-- url     : https://prove2.me/submissions/2a34a5e6-bf82-4c67-861c-3e4d70306ad9

-- Generated proof for MIPStarRE.QPBT.MagicSquareRigidity.msCellObsA_prod_of.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Test_MagicSquare
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_CellRelations
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Dilation
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Reflections
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Relations
import Theorems.Thm_MIPStarRE_QPBT_MagicSquareRigidity_mul_eq_zero_of_isProj_of_add_le_one
import Theorems.Thm_MIPStarRE_QPBT_MagicSquareRigidity_naimarkDilatedEffect_isProj

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT.MagicSquareRigidity
end MIPStarRE.QPBT.MagicSquareRigidity
namespace MIPStarRE.QPBT.MagicSquareRigidity.NormCloseOn
end MIPStarRE.QPBT.MagicSquareRigidity.NormCloseOn

/- Source helpers from QPBT/Test/MagicSquareTheorems/Rigidity/Dilation.lean. -/
/-!
# A simultaneous projective dilation of a Magic Square strategy

The rigidity argument for the Magic Square game is stated for an arbitrary
tensor-product strategy, whose measurements are positive operator valued
measures.  The self-testing argument, however, manipulates projections.  This
file removes that discrepancy by dilating an arbitrary strategy to a projective
one without changing any observable quantity.

Each local Hilbert space `ℂ^ι` is enlarged by one auxiliary register whose
basis is indexed by `Option MsAnswer`, and the original space is identified with
the *ground slice* `ℂ^ι ⊗ |⊥⟩`.  The one-measurement Naimark lemma of the low
individual degree development supplies, for every question separately, a family
of projections on the enlarged space whose compression to the ground slice
returns the original effects; the ancilla is the same for all questions, so the
identification of `ℂ^ι` with the ground slice is a single isometry serving every
question at once.  Folding the deficiency `1 - ∑_a P_a` into one distinguished
answer turns the dilated family into a complete projective measurement without
disturbing the compression, because the original effects already sum to the
identity.

Since the dilated state is the image of the original state under the two ground
embeddings, every Born probability, and hence the game value and all the
rejection, malformed-answer, cell-consistency and parity masses of the
value-to-parity layer, is unchanged.  Conversely, the local isometries produced
by a rigidity argument applied to the dilated strategy compose with the ground
embeddings to give local isometries of the original strategy, and the
state-dependent norms occurring in the conclusion of `thm:ms-rigidity` transfer
along that composition.

## References

The rigidity statement supported here is blueprint
`thm:ms-rigidity`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`,
proved in Coladangelo--Stark, Theorem 6.9.  The dilation reuses the
one-measurement Naimark lemma of
`references/ldt-paper/orthonormalization.tex:121-159`, formalized as
`MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimark`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective

noncomputable section

/-! ## Orthogonality inside a subnormalized family of projections -/



/-- Formalization-only auxiliary lemma for the dilation of `thm:ms-rigidity`
(blueprint `thm:ms-rigidity`).  A finite family of orthogonal
projections whose sum is at most the identity is mutually orthogonal: for two
distinct indices the two projections already sum to at most the identity, so the
previous lemma applies. -/
theorem mul_eq_zero_of_isProj_family {d α : Type*} [Fintype d] [DecidableEq d]
    [Fintype α] {P : α → _root_.LIDT.MIPStarRE.Quantum.Op d} (hP : ∀ a, _root_.LIDT.MIPStarRE.Quantum.IsProj (P a))
    (hsum : ∑ a, P a ≤ 1) {a b : α} (hab : a ≠ b) :
    P a * P b = 0 := by
  classical
  refine _root_.MIPStarRE.QPBT.MagicSquareRigidity.mul_eq_zero_of_isProj_of_add_le_one (hP a) (hP b).nonneg ?_
  refine le_trans ?_ hsum
  have hpair : ∑ c ∈ ({a, b} : Finset α), P c = P a + P b := by
    rw [Finset.sum_pair hab]
  rw [← hpair]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun c _ _ => (hP c).nonneg)



/-! ## The ground slice of an enlarged local space -/



























/-! ## The dilated projective measurement -/





















/-- The dilated measurement is projective, which is the property the self-testing
argument of `thm:ms-rigidity` uses. -/
theorem naimarkDilatedMeasurement_isProjective {α d : Type} [Fintype α] [DecidableEq α]
    [Fintype d] [DecidableEq d] (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α d) (a₀ : α) :
    _root_.MIPStarRE.QPBT.Measurement.IsProjective (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedMeasurement M a₀) :=
  fun a => _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedEffect_isProj M a₀ a



/-! ## The dilated state -/













/-! ## The dilated Magic Square strategy -/









/-- Every question measurement of the dilated strategy is projective, which is
the hypothesis under which the Coladangelo--Stark self-test is stated. -/
theorem msDilatedStrategy_isProjective_A (S : _root_.MIPStarRE.QPBT.Strategy _root_.MIPStarRE.QPBT.msGame) (x : _root_.MIPStarRE.QPBT.MsType) :
    _root_.MIPStarRE.QPBT.Measurement.IsProjective ((_root_.MIPStarRE.QPBT.MagicSquareRigidity.msDilatedStrategy S).A x) :=
  _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedMeasurement_isProjective (α := _root_.MIPStarRE.QPBT.MsAnswer) (S.A x) (_root_.MIPStarRE.QPBT.MsAnswer.bit 0)



/-! ## Preservation of the value-to-parity layer -/



































/-! ## Composition of the dilation with later local isometries -/



















/-! ## Transfer of state-dependent bounds -/

















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





/-! ## Sign observables of a projective measurement -/

section SignObs

variable {α d : Type} [Fintype α] [DecidableEq α] [Fintype d] [DecidableEq d]





omit [DecidableEq α] in
/-- Formalization-only: the effects of a projective measurement are mutually
orthogonal, so two spectral combinations of them multiply coefficientwise. -/
private theorem sum_smul_effect_mul (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α d)
    (hM : _root_.MIPStarRE.QPBT.Measurement.IsProjective M) (c e : α → ℂ) :
    (∑ a, c a • M.effect a) * (∑ a, e a • M.effect a) =
      ∑ a, (c a * e a) • M.effect a := by
  classical
  have horth : ∀ a b : α, a ≠ b → M.effect a * M.effect b = 0 := fun a b hab =>
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.mul_eq_zero_of_isProj_family hM M.sum_le_one hab
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hidem : M.effect a * M.effect a = M.effect a := (hM a).isIdempotentElem
  rw [Matrix.smul_mul, Matrix.mul_sum, Finset.smul_sum, Finset.sum_eq_single a]
  · rw [Matrix.mul_smul, smul_smul, hidem]
  · intro b _ hba
    rw [Matrix.mul_smul, horth a b (Ne.symm hba), smul_zero, smul_zero]
  · intro ha
    exact absurd (Finset.mem_univ a) ha

omit [DecidableEq α] in
/-- Sign observables of one projective measurement multiply by adding their
relabellings. -/
theorem signObs_mul (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α d)
    (hM : _root_.MIPStarRE.QPBT.Measurement.IsProjective M) (f g : α → ZMod 2) :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.signObs M f * _root_.MIPStarRE.QPBT.MagicSquareRigidity.signObs M g = _root_.MIPStarRE.QPBT.MagicSquareRigidity.signObs M (fun a => f a + g a) := by
  rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.signObs, _root_.MIPStarRE.QPBT.MagicSquareRigidity.signObs, sum_smul_effect_mul M hM, _root_.MIPStarRE.QPBT.MagicSquareRigidity.signObs]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Complex.ofReal_mul, ← _root_.MIPStarRE.QPBT.MagicSquareRigidity.bit_sign_add]











end SignObs

/-! ## Deviation of joint spectral combinations on the strategy state -/



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

















/-! ## Agreement of the two reflections attached to a common cell -/





/-! ## Permuted row and column products -/

theorem solution (S : _root_.MIPStarRE.QPBT.Strategy _root_.MIPStarRE.QPBT.msGame) (i : Fin 6) (k₀ k₁ k₂ : Fin 3)
    (hsum : ∀ a, _root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitOrZero k₀ a + _root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitOrZero k₁ a +
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitOrZero k₂ a = _root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitSum a) :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.msCellObsA S i k₀ * _root_.MIPStarRE.QPBT.MagicSquareRigidity.msCellObsA S i k₁ * _root_.MIPStarRE.QPBT.MagicSquareRigidity.msCellObsA S i k₂ =
      _root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.MagicSquareRigidity.signObs ((_root_.MIPStarRE.QPBT.MagicSquareRigidity.msDilatedStrategy S).A (_root_.MIPStarRE.QPBT.MsType.constraint i))
        _root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitSum) 1 := by
  have hkey : _root_.MIPStarRE.QPBT.MagicSquareRigidity.signObs ((_root_.MIPStarRE.QPBT.MagicSquareRigidity.msDilatedStrategy S).A (_root_.MIPStarRE.QPBT.MsType.constraint i))
        (_root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitOrZero k₀) *
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.signObs ((_root_.MIPStarRE.QPBT.MagicSquareRigidity.msDilatedStrategy S).A (_root_.MIPStarRE.QPBT.MsType.constraint i)) (_root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitOrZero k₁) *
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.signObs ((_root_.MIPStarRE.QPBT.MagicSquareRigidity.msDilatedStrategy S).A (_root_.MIPStarRE.QPBT.MsType.constraint i)) (_root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitOrZero k₂) =
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.signObs ((_root_.MIPStarRE.QPBT.MagicSquareRigidity.msDilatedStrategy S).A (_root_.MIPStarRE.QPBT.MsType.constraint i)) _root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitSum := by
    rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.signObs_mul _ (_root_.MIPStarRE.QPBT.MagicSquareRigidity.msDilatedStrategy_isProjective_A S _),
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.signObs_mul _ (_root_.MIPStarRE.QPBT.MagicSquareRigidity.msDilatedStrategy_isProjective_A S _)]
    congr 1
    funext a
    exact hsum a
  rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.msCellObsA, _root_.MIPStarRE.QPBT.MagicSquareRigidity.msCellObsA, _root_.MIPStarRE.QPBT.MagicSquareRigidity.msCellObsA, _root_.MIPStarRE.QPBT.heteroKron_mul, _root_.MIPStarRE.QPBT.heteroKron_mul]
  simp only [mul_one]
  rw [hkey]
