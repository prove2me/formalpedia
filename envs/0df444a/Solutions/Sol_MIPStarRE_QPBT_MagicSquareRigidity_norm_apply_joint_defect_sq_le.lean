-- Prove2me | solution 1 for MIPStarRE.QPBT.MagicSquareRigidity.norm_apply_joint_defect_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:27:31.361531+00:00
-- url     : https://prove2.me/submissions/eee340f2-4786-4bce-870f-d410b8d5d00a

-- Generated proof for MIPStarRE.QPBT.MagicSquareRigidity.norm_apply_joint_defect_sq_le.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_GroundSlice
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Reflections
import Theorems.Thm_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_isProj_kronecker
import Theorems.Thm_MIPStarRE_QPBT_MagicSquareRigidity_mul_eq_zero_of_isProj_of_add_le_one

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.MagicSquareRigidity
end MIPStarRE.QPBT.MagicSquareRigidity
namespace MIPStarRE.QPBT.MagicSquareRigidity.NormCloseOn
end MIPStarRE.QPBT.MagicSquareRigidity.NormCloseOn

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

























end MIPStarRE.QPBT

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

























/-! ## The dilated state -/













/-! ## The dilated Magic Square strategy -/













/-! ## Preservation of the value-to-parity layer -/



































/-! ## Composition of the dilation with later local isometries -/



















/-! ## Transfer of state-dependent bounds -/

















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

section StateNorm

variable {ι : Type} [Fintype ι] [DecidableEq ι]





/-- Formalization-only: acting by a finite sum of operators is the sum of the
actions. -/
theorem applyOperatorToState_sum {γ : Type} [Fintype γ]
    (M : γ → _root_.LIDT.MIPStarRE.Quantum.Op ι) (ψ : EuclideanSpace ℂ ι) :
    _root_.MIPStarRE.QPBT.applyOperatorToState (∑ c, M c) ψ = ∑ c, _root_.MIPStarRE.QPBT.applyOperatorToState (M c) ψ := by
  unfold _root_.MIPStarRE.QPBT.applyOperatorToState
  simp only [map_sum, LinearMap.sum_apply]





end StateNorm

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













end SignObs

/-! ## Deviation of joint spectral combinations on the strategy state -/

section JointDefect



/-- Formalization-only: a real spectral combination of the effects of a
projective measurement is self-adjoint. -/
private theorem sum_real_smul_effect_conjTranspose {α d : Type} [Fintype α]
    [Fintype d] [DecidableEq d] (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α d)
    (hM : _root_.MIPStarRE.QPBT.Measurement.IsProjective M) (c : α → ℝ) :
    (∑ a, ((c a : ℝ) : ℂ) • M.effect a)ᴴ = ∑ a, ((c a : ℝ) : ℂ) • M.effect a := by
  rw [← Matrix.star_eq_conjTranspose, star_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [star_smul]
  congr 1
  · simp
  · exact (hM a).isSelfAdjoint

/-- Formalization-only: the quadratic form of a real spectral combination on a
state is the corresponding real combination of the individual quadratic
forms. -/
private theorem re_inner_apply_sum_real_smul {ι γ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype γ] (r : γ → ℝ) (K : γ → _root_.LIDT.MIPStarRE.Quantum.Op ι) (ψ : EuclideanSpace ℂ ι) :
    (inner ℂ ψ (_root_.MIPStarRE.QPBT.applyOperatorToState (∑ c, ((r c : ℝ) : ℂ) • K c) ψ)).re =
      ∑ c, r c * (inner ℂ ψ (_root_.MIPStarRE.QPBT.applyOperatorToState (K c) ψ)).re := by
  rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.applyOperatorToState_sum, inner_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.applyOperatorToState_smul, inner_smul_right]
  simp

variable {G : _root_.MIPStarRE.QPBT.Game}





/-- Formalization-only: the quadratic form of a joint effect is the Born weight
of the corresponding answer pair. -/
private theorem re_inner_jointMeasurement_effect (T : _root_.MIPStarRE.QPBT.Strategy G) (x : G.QuestionA)
    (y : G.QuestionB) (ab : G.AnswerA × G.AnswerB) :
    (inner ℂ T.ψ (_root_.MIPStarRE.QPBT.applyOperatorToState ((jointMeasurement T x y).effect ab) T.ψ)).re =
      _root_.MIPStarRE.QPBT.outcomeWeight T x y ab.1 ab.2 := rfl







end JointDefect

end

end MIPStarRE.QPBT.MagicSquareRigidity

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



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT.MagicSquareRigidity

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum



/-! ## Rectangular tensor placement -/













/-! ## The state-dependent norm -/



variable {ι : Type} [Fintype ι] [DecidableEq ι]













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



open MIPStarRE.QPBT.MagicSquareRigidity.NormCloseOn

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {ψ : EuclideanSpace ℂ ι} {δ η : ℝ} {M N P U : _root_.LIDT.MIPStarRE.Quantum.Op ι}





















/-! ## Sign observables of a projective measurement -/



variable {α d : Type} [Fintype α] [DecidableEq α] [Fintype d] [DecidableEq d]





















/-! ## Deviation of joint spectral combinations on the strategy state -/









variable {G : _root_.MIPStarRE.QPBT.Game}

theorem solution (T : _root_.MIPStarRE.QPBT.Strategy G) (x : G.QuestionA)
    (y : G.QuestionB) (hA : _root_.MIPStarRE.QPBT.Measurement.IsProjective (T.A x))
    (hB : _root_.MIPStarRE.QPBT.Measurement.IsProjective (T.B y))
    (coef : G.AnswerA → G.AnswerB → ℝ) (E : G.AnswerA → G.AnswerB → Prop)
    [DecidableRel E] (hbound : ∀ a b, coef a b ^ 2 ≤ 4)
    (hsupp : ∀ a b, ¬ E a b → coef a b = 0) :
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState
        (∑ a : G.AnswerA, ∑ b : G.AnswerB, ((coef a b : ℝ) : ℂ) •
          _root_.MIPStarRE.QPBT.heteroKron ((T.A x).effect a) ((T.B y).effect b)) T.ψ‖ ^ 2 ≤
      4 * _root_.MIPStarRE.QPBT.outcomeEventWeight T x y E := by
  classical
  set J := jointMeasurement T x y with hJ
  have hJproj : _root_.MIPStarRE.QPBT.Measurement.IsProjective J := fun ab =>
    _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.isProj_kronecker (hA ab.1) (hB ab.2)
  have hcollapse : (∑ a : G.AnswerA, ∑ b : G.AnswerB, ((coef a b : ℝ) : ℂ) •
      _root_.MIPStarRE.QPBT.heteroKron ((T.A x).effect a) ((T.B y).effect b)) =
      ∑ ab : G.AnswerA × G.AnswerB, ((coef ab.1 ab.2 : ℝ) : ℂ) • J.effect ab := by
    rw [Fintype.sum_prod_type]
    rfl
  have hsa : (∑ ab : G.AnswerA × G.AnswerB, ((coef ab.1 ab.2 : ℝ) : ℂ) • J.effect ab)ᴴ =
      ∑ ab : G.AnswerA × G.AnswerB, ((coef ab.1 ab.2 : ℝ) : ℂ) • J.effect ab :=
    sum_real_smul_effect_conjTranspose J hJproj (fun ab => coef ab.1 ab.2)
  have hsq : ∀ ab : G.AnswerA × G.AnswerB,
      ((coef ab.1 ab.2 : ℝ) : ℂ) * ((coef ab.1 ab.2 : ℝ) : ℂ) =
        ((coef ab.1 ab.2 ^ 2 : ℝ) : ℂ) := by
    intro ab
    rw [← Complex.ofReal_mul, sq]
  rw [hcollapse, _root_.MIPStarRE.QPBT.MagicSquareRigidity.norm_applyOperatorToState_sq, hsa,
    sum_smul_effect_mul J hJproj]
  simp only [hsq]
  rw [re_inner_apply_sum_real_smul]
  have hterm : ∀ ab : G.AnswerA × G.AnswerB,
      coef ab.1 ab.2 ^ 2 *
          (inner ℂ T.ψ (_root_.MIPStarRE.QPBT.applyOperatorToState (J.effect ab) T.ψ)).re ≤
        (if E ab.1 ab.2 then 4 * _root_.MIPStarRE.QPBT.outcomeWeight T x y ab.1 ab.2 else 0) := by
    intro ab
    have hw : 0 ≤ _root_.MIPStarRE.QPBT.outcomeWeight T x y ab.1 ab.2 := _root_.MIPStarRE.QPBT.outcomeWeight_nonneg T x y ab.1 ab.2
    rw [re_inner_jointMeasurement_effect]
    by_cases hE : E ab.1 ab.2
    · rw [if_pos hE]
      exact mul_le_mul_of_nonneg_right (hbound ab.1 ab.2) hw
    · rw [if_neg hE, hsupp ab.1 ab.2 hE]
      simp
  calc ∑ ab : G.AnswerA × G.AnswerB, coef ab.1 ab.2 ^ 2 *
        (inner ℂ T.ψ (_root_.MIPStarRE.QPBT.applyOperatorToState (J.effect ab) T.ψ)).re
      ≤ ∑ ab : G.AnswerA × G.AnswerB,
          (if E ab.1 ab.2 then 4 * _root_.MIPStarRE.QPBT.outcomeWeight T x y ab.1 ab.2 else 0) :=
        Finset.sum_le_sum fun ab _ => hterm ab
    _ = 4 * _root_.MIPStarRE.QPBT.outcomeEventWeight T x y E := by
        rw [Fintype.sum_prod_type, _root_.MIPStarRE.QPBT.outcomeEventWeight, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        by_cases hE : E a b <;> simp [hE]
