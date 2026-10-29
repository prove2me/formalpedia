-- Prove2me | solution 1 for MIPStarRE.QPBT.MagicSquareRigidity.msVarObsB_anticommute
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:53:52.692031+00:00
-- url     : https://prove2.me/submissions/6c5d5406-aa33-42c7-8adf-5abd66b1a38c

-- Generated proof for MIPStarRE.QPBT.MagicSquareRigidity.msVarObsB_anticommute.
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
import Definitions.Def_QPBT_QPBT_Combining_Linearity_Defs
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Test_MagicSquare
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_CellRelations
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Dilation
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_GroundSlice
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Reflections
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Relations
import Theorems.Thm_MIPStarRE_QPBT_MagicSquareRigidity_msCellObsA_close_msVarObsB
import Theorems.Thm_MIPStarRE_QPBT_MagicSquareRigidity_msCellObsA_mul_close_of_same_cells
import Theorems.Thm_MIPStarRE_QPBT_MagicSquareRigidity_msCellObsA_step
import Theorems.Thm_MIPStarRE_QPBT_MagicSquareRigidity_mul_eq_zero_of_isProj_of_add_le_one
import Theorems.Thm_MIPStarRE_QPBT_MagicSquareRigidity_naimarkDilatedEffect_isProj

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.IsBinaryObservable
end MIPStarRE.QPBT.IsBinaryObservable
namespace MIPStarRE.QPBT.MagicSquareRigidity
end MIPStarRE.QPBT.MagicSquareRigidity
namespace MIPStarRE.QPBT.MagicSquareRigidity.NormCloseOn
end MIPStarRE.QPBT.MagicSquareRigidity.NormCloseOn

/- Source helpers from QPBT/Combining/Linearity/Defs.lean. -/
/-!
# Binary observables and the state-dependent distance

This file collects the notions in which the quantum linearity theorem of
Natarajan and Vidick is stated: binary observables, the rank-one density
operator of an ancillary vector, and the squared state-dependent distance
between two operators weighted by a positive semidefinite trace-one operator.
The theorem itself, `exists_exactly_linear_observables`, is stated and proved
in `MIPStarRE/QPBT/Combining/Linearity.lean` from the Boolean Fourier,
operator BLR, Naimark rounding, and representation stability modules under
`MIPStarRE/QPBT/Combining/Linearity/`, all of which build on this file.

## Main definitions

* `IsBinaryObservable`: a Hermitian operator whose square is the identity,
  together with its algebra: the identity is a binary observable, so is the
  product of two commuting ones, every binary observable is an isometry, and it
  remains one after ampliation by the identity of another tensor factor.
* `ancProj`: the rank-one density operator `|v⟩⟨v|` of a vector `v`.
* `stateDepDistSq`: the squared state-dependent distance
  `d_ρ(S, T)^2 = Re Tr((S - T)^† (S - T) ρ)`.

## References

The notions are those of blueprint
`thm:linearity`, quoted in the QPBT
paper at `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:713-725`
from Theorem 10 of Natarajan--Vidick, arXiv:1610.03574,
`references/nv-paper/fullpaper.tex:1074-1088`; the state-dependent distance is
defined there at lines 866--875.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.Quantum

noncomputable section





/-- The ampliation `O ⊗ 1` of a binary observable by the identity of a second
tensor factor is a binary observable.  This is the sense in which the original
observables `A(a)` act on the extended space in display (8) of
`references/nv-paper/fullpaper.tex:1083-1086`; it is also the way a Magic Square
observable of one player acts on the joint space of `thm:ms-rigidity`. -/
theorem isBinaryObservable_heteroKron_one {ι ι' : Type} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι'] {O : _root_.LIDT.MIPStarRE.Quantum.Op ι} (hO : _root_.MIPStarRE.QPBT.IsBinaryObservable O) :
    _root_.MIPStarRE.QPBT.IsBinaryObservable (_root_.MIPStarRE.QPBT.heteroKron O (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι')) := by
  unfold _root_.MIPStarRE.QPBT.heteroKron
  simp only [Matrix.kronecker]
  refine ⟨?_, ?_⟩
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_kronecker, hO.conjTranspose_eq,
      Matrix.conjTranspose_one]
  · rw [← Matrix.mul_kronecker_mul, hO.mul_self_eq_one, Matrix.one_mul,
      Matrix.one_kronecker_one]

/-- The ampliation `1 ⊗ O` of a binary observable by the identity of the first
tensor factor is a binary observable; this is the mirror of
`isBinaryObservable_heteroKron_one` for the second player's factor in
blueprint `thm:ms-rigidity`. -/
theorem isBinaryObservable_one_heteroKron {ι ι' : Type} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι'] {O : _root_.LIDT.MIPStarRE.Quantum.Op ι'} (hO : _root_.MIPStarRE.QPBT.IsBinaryObservable O) :
    _root_.MIPStarRE.QPBT.IsBinaryObservable (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) O) := by
  unfold _root_.MIPStarRE.QPBT.heteroKron
  simp only [Matrix.kronecker]
  refine ⟨?_, ?_⟩
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_kronecker, hO.conjTranspose_eq,
      Matrix.conjTranspose_one]
  · rw [← Matrix.mul_kronecker_mul, hO.mul_self_eq_one, Matrix.one_mul,
      Matrix.one_kronecker_one]





end

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

/-- Every question measurement of the dilated strategy is projective on Bob's
side as well. -/
theorem msDilatedStrategy_isProjective_B (S : _root_.MIPStarRE.QPBT.Strategy _root_.MIPStarRE.QPBT.msGame) (y : _root_.MIPStarRE.QPBT.MsType) :
    _root_.MIPStarRE.QPBT.Measurement.IsProjective ((_root_.MIPStarRE.QPBT.MagicSquareRigidity.msDilatedStrategy S).B y) :=
  _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedMeasurement_isProjective (α := _root_.MIPStarRE.QPBT.MsAnswer) (S.B y) (_root_.MIPStarRE.QPBT.MsAnswer.bit 0)

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

/-- Operators placed on the two tensor factors commute. -/
theorem heteroKron_comm {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB] (X : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (Y : _root_.LIDT.MIPStarRE.Quantum.Op ιB) :
    _root_.MIPStarRE.QPBT.heteroKron X (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιB) * _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιA) Y =
      _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιA) Y * _root_.MIPStarRE.QPBT.heteroKron X (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιB) := by
  rw [_root_.MIPStarRE.QPBT.heteroKron_mul, _root_.MIPStarRE.QPBT.heteroKron_mul, mul_one, one_mul, one_mul, mul_one]

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

/-- Multiplying on the left by an isometric operator preserves closeness. -/
theorem isometry_mul (hU : Uᴴ * U = 1) (h : _root_.MIPStarRE.QPBT.MagicSquareRigidity.NormCloseOn ψ δ M N) :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.NormCloseOn ψ δ (U * M) (U * N) := by
  have hsub : U * M - U * N = U * (M - N) := by noncomm_ring
  rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.NormCloseOn, hsub, _root_.MIPStarRE.QPBT.MagicSquareRigidity.norm_applyOperatorToState_isometry_mul hU]
  exact h

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

omit [DecidableEq α] in
/-- The sign observable of the zero relabelling is the identity. -/
theorem signObs_const_zero (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α d) :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.signObs M (fun _ => 0) = 1 := by
  have hb : ((_root_.MIPStarRE.QPBT.MagicSquareRigidity.bitSign (0 : ZMod 2) : ℝ) : ℂ) = 1 := by norm_num [_root_.MIPStarRE.QPBT.MagicSquareRigidity.bitSign]
  rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.signObs]
  simp only [hb, one_smul]
  exact M.sum_eq_one

omit [DecidableEq α] in
/-- A sign observable of a projective measurement is an involution. -/
theorem signObs_mul_self (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α d)
    (hM : _root_.MIPStarRE.QPBT.Measurement.IsProjective M) (f : α → ZMod 2) :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.signObs M f * _root_.MIPStarRE.QPBT.MagicSquareRigidity.signObs M f = 1 := by
  rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.signObs_mul M hM]
  have hzero : (fun a => f a + f a) = fun _ : α => (0 : ZMod 2) := by
    funext a
    exact (by decide : ∀ x : ZMod 2, x + x = 0) (f a)
  rw [hzero, _root_.MIPStarRE.QPBT.MagicSquareRigidity.signObs_const_zero]

omit [DecidableEq α] in
/-- A sign observable of a projective measurement is self-adjoint. -/
theorem signObs_conjTranspose (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α d)
    (hM : _root_.MIPStarRE.QPBT.Measurement.IsProjective M) (f : α → ZMod 2) :
    (_root_.MIPStarRE.QPBT.MagicSquareRigidity.signObs M f)ᴴ = _root_.MIPStarRE.QPBT.MagicSquareRigidity.signObs M f := by
  rw [← Matrix.star_eq_conjTranspose, _root_.MIPStarRE.QPBT.MagicSquareRigidity.signObs, star_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [star_smul]
  congr 1
  · simp
  · exact (hM a).isSelfAdjoint

omit [DecidableEq α] in
/-- A sign observable of a projective measurement is a binary observable, the
reflection attached to the relabelling `f`. -/
theorem isBinaryObservable_signObs (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α d)
    (hM : _root_.MIPStarRE.QPBT.Measurement.IsProjective M) (f : α → ZMod 2) :
    _root_.MIPStarRE.QPBT.IsBinaryObservable (_root_.MIPStarRE.QPBT.MagicSquareRigidity.signObs M f) :=
  ⟨_root_.MIPStarRE.QPBT.MagicSquareRigidity.signObs_conjTranspose M hM f, _root_.MIPStarRE.QPBT.MagicSquareRigidity.signObs_mul_self M hM f⟩



end SignObs

/-! ## Deviation of joint spectral combinations on the strategy state -/



end

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







/-! ## Comparison of Born masses with the game error -/







/-! ## The Magic Square reflections of the dilated strategy -/













/-- Alice's cell operators are binary observables. -/
theorem isBinaryObservable_msCellObsA (S : _root_.MIPStarRE.QPBT.Strategy _root_.MIPStarRE.QPBT.msGame) (i : Fin 6) (k : Fin 3) :
    _root_.MIPStarRE.QPBT.IsBinaryObservable (_root_.MIPStarRE.QPBT.MagicSquareRigidity.msCellObsA S i k) :=
  _root_.MIPStarRE.QPBT.isBinaryObservable_heteroKron_one
    (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isBinaryObservable_signObs _ (_root_.MIPStarRE.QPBT.MagicSquareRigidity.msDilatedStrategy_isProjective_A S _) _)





/-- Bob's variable operators are binary observables. -/
theorem isBinaryObservable_msVarObsB (S : _root_.MIPStarRE.QPBT.Strategy _root_.MIPStarRE.QPBT.msGame) (j : Fin 9) :
    _root_.MIPStarRE.QPBT.IsBinaryObservable (_root_.MIPStarRE.QPBT.MagicSquareRigidity.msVarObsB S j) :=
  _root_.MIPStarRE.QPBT.isBinaryObservable_one_heteroKron
    (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isBinaryObservable_signObs _ (_root_.MIPStarRE.QPBT.MagicSquareRigidity.msDilatedStrategy_isProjective_B S _) _)





/-- Alice's cell reflection commutes exactly with Bob's variable reflection. -/
theorem msCellObsA_comm_msVarObsB (S : _root_.MIPStarRE.QPBT.Strategy _root_.MIPStarRE.QPBT.msGame) (i : Fin 6) (k : Fin 3)
    (j : Fin 9) :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.msCellObsA S i k * _root_.MIPStarRE.QPBT.MagicSquareRigidity.msVarObsB S j = _root_.MIPStarRE.QPBT.MagicSquareRigidity.msVarObsB S j * _root_.MIPStarRE.QPBT.MagicSquareRigidity.msCellObsA S i k :=
  _root_.MIPStarRE.QPBT.MagicSquareRigidity.heteroKron_comm _ _







/-! ## The six row and column product relations -/

















/-! ## Agreement of the two reflections attached to a common cell -/





/-! ## Permuted row and column products -/









/-! ## The two logical Pauli pairs -/

























/-! ## Unit scalars -/







/-! ## Building blocks of the solution-group computation -/







end

end MIPStarRE.QPBT.MagicSquareRigidity

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



/-- A product of two of Alice's cell reflections is close, on the dilated state,
to the product of Bob's variable reflections at the same two cells, taken in the
reverse order. -/
theorem msCellObsA_mul_close (S : _root_.MIPStarRE.QPBT.Strategy _root_.MIPStarRE.QPBT.msGame) (ε : ℝ) (hwin : 1 - ε ≤ S.value)
    (I J : Fin 6) (k l : Fin 3) :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.NormCloseOn (_root_.MIPStarRE.QPBT.MagicSquareRigidity.msDilatedStrategy S).ψ (12 * Real.sqrt ε + 12 * Real.sqrt ε)
      (_root_.MIPStarRE.QPBT.MagicSquareRigidity.msCellObsA S I k * _root_.MIPStarRE.QPBT.MagicSquareRigidity.msCellObsA S J l)
      (_root_.MIPStarRE.QPBT.MagicSquareRigidity.msVarObsB S (_root_.MIPStarRE.QPBT.msConstraintVars J l) * _root_.MIPStarRE.QPBT.MagicSquareRigidity.msVarObsB S (_root_.MIPStarRE.QPBT.msConstraintVars I k)) := by
  have h1 : _root_.MIPStarRE.QPBT.MagicSquareRigidity.NormCloseOn (_root_.MIPStarRE.QPBT.MagicSquareRigidity.msDilatedStrategy S).ψ (12 * Real.sqrt ε)
      (_root_.MIPStarRE.QPBT.MagicSquareRigidity.msCellObsA S I k * _root_.MIPStarRE.QPBT.MagicSquareRigidity.msCellObsA S J l)
      (_root_.MIPStarRE.QPBT.MagicSquareRigidity.msCellObsA S I k * _root_.MIPStarRE.QPBT.MagicSquareRigidity.msVarObsB S (_root_.MIPStarRE.QPBT.msConstraintVars J l)) :=
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.NormCloseOn.isometry_mul (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isBinaryObservable_msCellObsA S I k).isometry
      (_root_.MIPStarRE.QPBT.MagicSquareRigidity.msCellObsA_close_msVarObsB S ε hwin J l)
  rw [show _root_.MIPStarRE.QPBT.MagicSquareRigidity.msCellObsA S I k * _root_.MIPStarRE.QPBT.MagicSquareRigidity.msVarObsB S (_root_.MIPStarRE.QPBT.msConstraintVars J l) =
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.msVarObsB S (_root_.MIPStarRE.QPBT.msConstraintVars J l) * _root_.MIPStarRE.QPBT.MagicSquareRigidity.msCellObsA S I k from
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.msCellObsA_comm_msVarObsB S I k (_root_.MIPStarRE.QPBT.msConstraintVars J l)] at h1
  exact h1.trans (_root_.MIPStarRE.QPBT.MagicSquareRigidity.NormCloseOn.isometry_mul (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isBinaryObservable_msVarObsB S _).isometry
    (_root_.MIPStarRE.QPBT.MagicSquareRigidity.msCellObsA_close_msVarObsB S ε hwin I k))











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





/-! ## The computation on Alice's cell reflections -/

theorem solution (S : _root_.MIPStarRE.QPBT.Strategy _root_.MIPStarRE.QPBT.msGame) (ε : ℝ) (hwin : 1 - ε ≤ S.value) :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.NormCloseOn (_root_.MIPStarRE.QPBT.MagicSquareRigidity.msDilatedStrategy S).ψ (624 * Real.sqrt ε)
      (_root_.MIPStarRE.QPBT.MagicSquareRigidity.msVarObsB S 0 * _root_.MIPStarRE.QPBT.MagicSquareRigidity.msVarObsB S 4) (-(_root_.MIPStarRE.QPBT.MagicSquareRigidity.msVarObsB S 4 * _root_.MIPStarRE.QPBT.MagicSquareRigidity.msVarObsB S 0)) := by
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
  have hsign_pos : ∀ i : Fin 6, i ≠ 5 → ((_root_.MIPStarRE.QPBT.MagicSquareRigidity.bitSign (_root_.MIPStarRE.QPBT.msParity i) : ℝ) : ℂ) = 1 := by
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
  have stepA := _root_.MIPStarRE.QPBT.MagicSquareRigidity.msCellObsA_step S ε hwin 0 4 1 0 2 0 1 2 hA hA' (by decide)
  rw [hsign_pos 0 (by decide), hsign_pos 4 (by decide), one_mul, one_smul] at stepA
  have stepB := _root_.MIPStarRE.QPBT.MagicSquareRigidity.msCellObsA_step S ε hwin 5 2 2 0 1 2 1 0 hB hB' (by decide)
  rw [hsign_neg, hsign_pos 2 (by decide), mul_one, neg_one_smul] at stepB
  have stepC := _root_.MIPStarRE.QPBT.MagicSquareRigidity.msCellObsA_step S ε hwin 1 3 0 2 1 1 2 0 hC hC' (by decide)
  rw [hsign_pos 1 (by decide), hsign_pos 3 (by decide), one_mul, one_smul] at stepC
  have linkA := _root_.MIPStarRE.QPBT.MagicSquareRigidity.msCellObsA_mul_close_of_same_cells S ε hwin 0 4 5 2 2 2 0 1
    (by decide) (by decide)
  have linkB := _root_.MIPStarRE.QPBT.MagicSquareRigidity.msCellObsA_mul_close_of_same_cells S ε hwin 5 2 1 3 1 0 2 2
    (by decide) (by decide)
  have linkC := _root_.MIPStarRE.QPBT.MagicSquareRigidity.msCellObsA_mul_close_of_same_cells S ε hwin 1 3 4 0 1 0 1 0
    (by decide) (by decide)
  have hstart := (_root_.MIPStarRE.QPBT.MagicSquareRigidity.msCellObsA_mul_close S ε hwin 0 4 0 1).symm
  have hend := _root_.MIPStarRE.QPBT.MagicSquareRigidity.msCellObsA_mul_close S ε hwin 4 0 1 0
  rw [show _root_.MIPStarRE.QPBT.msConstraintVars 4 1 = 4 from by decide,
    show _root_.MIPStarRE.QPBT.msConstraintVars 0 0 = 0 from by decide] at hstart hend
  have hchain := ((((((hstart.trans stepA).trans linkA).trans stepB).trans
    linkB.neg).trans stepC.neg).trans linkC.neg).trans hend.neg
  exact _root_.MIPStarRE.QPBT.MagicSquareRigidity.normCloseOn_neg_swap (hchain.mono (by linarith))
