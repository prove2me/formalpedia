-- Prove2me | solution 1 for MIPStarRE.QPBT.MagicSquareRigidity.msCellObsB_prod_close
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:41:35.180343+00:00
-- url     : https://prove2.me/submissions/9cda6c87-0eb9-4a4e-a397-a1112c70b525

-- Generated proof for MIPStarRE.QPBT.MagicSquareRigidity.msCellObsB_prod_close.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Games_CondLinear
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Test_MagicSquare
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_CellRelations
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Dilation
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Reflections
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Relations
import Theorems.Thm_MIPStarRE_QPBT_MagicSquareRigidity_constraintParityFailure_of_bitSum_ne
import Theorems.Thm_MIPStarRE_QPBT_MagicSquareRigidity_mul_eq_zero_of_isProj_of_add_le_one
import Theorems.Thm_MIPStarRE_QPBT_MagicSquareRigidity_naimarkCompression_naimarkDilatedEffect
import Theorems.Thm_MIPStarRE_QPBT_MagicSquareRigidity_naimarkDilatedEffect_isProj
import Theorems.Thm_MIPStarRE_QPBT_MagicSquareRigidity_norm_alice_sub_bob_signObs_sq_le
import Theorems.Thm_MIPStarRE_QPBT_MagicSquareRigidity_rejection_mass_le_thirty_six_mul_total
import Theorems.Thm_MIPStarRE_QPBT_MagicSquareRigidity_total_rejection_mass_eq_one_sub_value
import Theorems.Thm_MIPStarRE_QPBT_outcome_event_weight_mono
import Theorems.Thm_MIPStarRE_QPBT_sum_outcome_weight_left

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



/-- An answer event depending only on Bob has its Bob marginal weight. -/
theorem outcome_event_weight_right_eq {G : _root_.MIPStarRE.QPBT.Game} (S : _root_.MIPStarRE.QPBT.Strategy G)
    (x : G.QuestionA) (y : G.QuestionB)
    (E : G.AnswerB → Prop) [DecidablePred E] :
    _root_.MIPStarRE.QPBT.outcomeEventWeight S x y (fun _ b => E b) = _root_.MIPStarRE.QPBT.bobEventWeight S y E := by
  unfold _root_.MIPStarRE.QPBT.outcomeEventWeight _root_.MIPStarRE.QPBT.bobEventWeight
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : E b
  · simp [hb, _root_.MIPStarRE.QPBT.sum_outcome_weight_left S x y b]
  · simp [hb]










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





/-- The quadratic form of an operator on a pure state, written out in the
computational basis.  Formalization-only support for the dilation of
blueprint `thm:ms-rigidity`. -/
theorem inner_applyOperatorToState {ι : Type} [Fintype ι] [DecidableEq ι]
    (K : _root_.LIDT.MIPStarRE.Quantum.Op ι) (u : EuclideanSpace ℂ ι) :
    inner ℂ u (_root_.MIPStarRE.QPBT.applyOperatorToState K u) =
      ∑ p : ι, ∑ q : ι, (starRingEnd ℂ) (u p) * (K p q * u q) := by
  simp [PiLp.inner_apply, RCLike.inner_apply, _root_.MIPStarRE.QPBT.applyOperatorToState,
    Matrix.mulVec, dotProduct, Finset.mul_sum, mul_comm]



/-- The quadratic form of a product operator on the dilated state agrees with the
quadratic form of the two ground-slice compressions on the original state.  This
is the identity that makes the dilation invisible to every observable quantity of
the strategy. -/
theorem inner_heteroKron_naimarkDilatedState (α : Type) [Fintype α] [DecidableEq α]
    {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (ψ : EuclideanSpace ℂ (ιA × ιB))
    (M : _root_.LIDT.MIPStarRE.Quantum.Op (ιA × Option α)) (N : _root_.LIDT.MIPStarRE.Quantum.Op (ιB × Option α)) :
    inner ℂ (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState α ψ)
        (_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron M N) (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState α ψ)) =
      inner ℂ ψ (_root_.MIPStarRE.QPBT.applyOperatorToState
        (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkCompression M) (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkCompression N)) ψ) := by
  classical
  rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.inner_applyOperatorToState, _root_.MIPStarRE.QPBT.MagicSquareRigidity.inner_applyOperatorToState]
  simp [Fintype.sum_prod_type, Fintype.sum_option, _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState_apply_mul,
    _root_.MIPStarRE.QPBT.heteroKron, Matrix.kroneckerMap_apply, mul_comm, mul_assoc]



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

/-- The dilation preserves every conditioned Born mass. -/
theorem ms_dilated_strategy_outcome_weight (S : _root_.MIPStarRE.QPBT.Strategy _root_.MIPStarRE.QPBT.msGame) (x y : _root_.MIPStarRE.QPBT.MsType)
    (a b : _root_.MIPStarRE.QPBT.MsAnswer) :
    _root_.MIPStarRE.QPBT.outcomeWeight (_root_.MIPStarRE.QPBT.MagicSquareRigidity.msDilatedStrategy S) x y a b = _root_.MIPStarRE.QPBT.outcomeWeight S x y a b := by
  change (inner ℂ (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState _root_.MIPStarRE.QPBT.MsAnswer S.ψ)
      (_root_.MIPStarRE.QPBT.applyOperatorToState
        (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedEffect (α := _root_.MIPStarRE.QPBT.MsAnswer) (S.A x) (_root_.MIPStarRE.QPBT.MsAnswer.bit 0) a)
          (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedEffect (α := _root_.MIPStarRE.QPBT.MsAnswer) (S.B y) (_root_.MIPStarRE.QPBT.MsAnswer.bit 0) b))
        (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState _root_.MIPStarRE.QPBT.MsAnswer S.ψ))).re =
    (inner ℂ S.ψ (_root_.MIPStarRE.QPBT.applyOperatorToState
      (_root_.MIPStarRE.QPBT.heteroKron ((S.A x).effect a) ((S.B y).effect b)) S.ψ)).re
  rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.inner_heteroKron_naimarkDilatedState, _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkCompression_naimarkDilatedEffect,
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkCompression_naimarkDilatedEffect]



/-- The dilation preserves Bob's marginal Born masses. -/
theorem ms_dilated_strategy_bob_outcome_weight (S : _root_.MIPStarRE.QPBT.Strategy _root_.MIPStarRE.QPBT.msGame) (y : _root_.MIPStarRE.QPBT.MsType)
    (b : _root_.MIPStarRE.QPBT.MsAnswer) :
    _root_.MIPStarRE.QPBT.bobOutcomeWeight (_root_.MIPStarRE.QPBT.MagicSquareRigidity.msDilatedStrategy S) y b = _root_.MIPStarRE.QPBT.bobOutcomeWeight S y b := by
  rw [← _root_.MIPStarRE.QPBT.sum_outcome_weight_left (_root_.MIPStarRE.QPBT.MagicSquareRigidity.msDilatedStrategy S) y y b,
    ← _root_.MIPStarRE.QPBT.sum_outcome_weight_left S y y b]
  exact Finset.sum_congr rfl fun a _ => _root_.MIPStarRE.QPBT.MagicSquareRigidity.ms_dilated_strategy_outcome_weight S y y a b





/-- The dilation preserves the mass of every event depending only on Bob's
answer. -/
theorem ms_dilated_strategy_bob_event_weight (S : _root_.MIPStarRE.QPBT.Strategy _root_.MIPStarRE.QPBT.msGame) (y : _root_.MIPStarRE.QPBT.MsType)
    (E : _root_.MIPStarRE.QPBT.MsAnswer → Prop) [DecidablePred E] :
    _root_.MIPStarRE.QPBT.bobEventWeight (_root_.MIPStarRE.QPBT.MagicSquareRigidity.msDilatedStrategy S) y E = _root_.MIPStarRE.QPBT.bobEventWeight S y E := by
  unfold _root_.MIPStarRE.QPBT.bobEventWeight
  exact Finset.sum_congr rfl fun b _ => by
    by_cases h : E b <;> simp [h, _root_.MIPStarRE.QPBT.MagicSquareRigidity.ms_dilated_strategy_bob_outcome_weight]





















/-- The dilation preserves Bob's row or column parity-failure mass. -/
theorem ms_dilated_strategy_bob_parity_failure_mass (S : _root_.MIPStarRE.QPBT.Strategy _root_.MIPStarRE.QPBT.msGame) (i : Fin 6) :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.bobParityFailureMass (_root_.MIPStarRE.QPBT.MagicSquareRigidity.msDilatedStrategy S) i = _root_.MIPStarRE.QPBT.MagicSquareRigidity.bobParityFailureMass S i :=
  _root_.MIPStarRE.QPBT.MagicSquareRigidity.ms_dilated_strategy_bob_event_weight S _ _

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









/-- A variable-to-constraint incidence belongs to the question support. -/
theorem ms_reverse_incidence_mem_support (i : Fin 6) (k : Fin 3) :
    (.var (_root_.MIPStarRE.QPBT.msConstraintVars i k), .constraint i) ∈
      (_root_.MIPStarRE.QPBT.graphDistribution _root_.MIPStarRE.QPBT.msEdges _root_.MIPStarRE.QPBT.msEdges_nonempty).support := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [Sym2.eq_swap]
  exact Finset.mem_image.mpr ⟨(i, k), Finset.mem_univ _, rfl⟩



/-! ## Rejection mass from the game value -/



















/-- Value at least `1 - ε` implies total rejection mass at most `ε`. -/
theorem total_rejection_mass_le (S : _root_.MIPStarRE.QPBT.Strategy _root_.MIPStarRE.QPBT.msGame) (ε : ℝ)
    (hwin : 1 - ε ≤ S.value) : _root_.MIPStarRE.QPBT.MagicSquareRigidity.totalRejectionMass S ≤ ε := by
  rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.total_rejection_mass_eq_one_sub_value]
  linarith





/-- A supported conditioned rejection mass is at most `36 * ε`. -/
theorem rejection_mass_le (S : _root_.MIPStarRE.QPBT.Strategy _root_.MIPStarRE.QPBT.msGame) (ε : ℝ)
    (hwin : 1 - ε ≤ S.value) {xy : _root_.MIPStarRE.QPBT.MsType × _root_.MIPStarRE.QPBT.MsType}
    (hxy : xy ∈ (_root_.MIPStarRE.QPBT.graphDistribution _root_.MIPStarRE.QPBT.msEdges _root_.MIPStarRE.QPBT.msEdges_nonempty).support) :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.rejectionMass S xy.1 xy.2 ≤ 36 * ε := by
  calc
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.rejectionMass S xy.1 xy.2 ≤ 36 * _root_.MIPStarRE.QPBT.MagicSquareRigidity.totalRejectionMass S :=
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.rejection_mass_le_thirty_six_mul_total S hxy
    _ ≤ 36 * ε :=
      mul_le_mul_of_nonneg_left (_root_.MIPStarRE.QPBT.MagicSquareRigidity.total_rejection_mass_le S ε hwin) (by norm_num)

/-- An event which always rejects has mass at most the conditioned rejection mass. -/
theorem outcome_event_weight_le_rejection_mass (S : _root_.MIPStarRE.QPBT.Strategy _root_.MIPStarRE.QPBT.msGame) (x y : _root_.MIPStarRE.QPBT.MsType)
    (E : _root_.MIPStarRE.QPBT.MsAnswer → _root_.MIPStarRE.QPBT.MsAnswer → Prop) [DecidableRel E]
    (hE : ∀ a b, E a b → _root_.MIPStarRE.QPBT.msWinPredicate x y a b = false) :
    _root_.MIPStarRE.QPBT.outcomeEventWeight S x y E ≤ _root_.MIPStarRE.QPBT.MagicSquareRigidity.rejectionMass S x y := by
  unfold _root_.MIPStarRE.QPBT.MagicSquareRigidity.rejectionMass
  letI : DecidableRel (fun a b : _root_.MIPStarRE.QPBT.MsAnswer => _root_.MIPStarRE.QPBT.msWinPredicate x y a b = false) :=
    fun _ _ => inferInstance
  exact _root_.MIPStarRE.QPBT.outcome_event_weight_mono S x y E _ hE

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

























private theorem reverse_parity_failure_rejects (i : Fin 6) (k : Fin 3)
    (a b : _root_.MIPStarRE.QPBT.MsAnswer) (hparity : _root_.MIPStarRE.QPBT.MagicSquareRigidity.ConstraintParityFailure i b) :
    _root_.MIPStarRE.QPBT.msWinPredicate (.var (_root_.MIPStarRE.QPBT.msConstraintVars i k)) (.constraint i) a b = false := by
  cases a with
  | triple α => rfl
  | bit γ =>
      cases b with
      | bit δ => rfl
      | triple β =>
          rw [_root_.MIPStarRE.QPBT.msWinPredicate, decide_eq_false_iff_not]
          intro haccept
          apply hparity
          unfold _root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintParityProduct
          calc
            (∏ l : Fin 3, _root_.MIPStarRE.QPBT.MagicSquareRigidity.bitSign (β l)) = _root_.MIPStarRE.QPBT.MagicSquareRigidity.bitSign (∑ l : Fin 3, β l) :=
              (_root_.MIPStarRE.QPBT.MagicSquareRigidity.bit_sign_sum_fin_three β).symm
            _ = _root_.MIPStarRE.QPBT.MagicSquareRigidity.bitSign (_root_.MIPStarRE.QPBT.msParity i) := by rw [haccept.1]



/-- Bob satisfies each of the six row or column sign products up to mass `36 * ε`. -/
theorem bob_parity_failure_mass_le (S : _root_.MIPStarRE.QPBT.Strategy _root_.MIPStarRE.QPBT.msGame) (ε : ℝ)
    (hwin : 1 - ε ≤ S.value) (i : Fin 6) :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.bobParityFailureMass S i ≤ 36 * ε := by
  unfold _root_.MIPStarRE.QPBT.MagicSquareRigidity.bobParityFailureMass
  rw [← _root_.MIPStarRE.QPBT.outcome_event_weight_right_eq S (.var (_root_.MIPStarRE.QPBT.msConstraintVars i 0)) (.constraint i)]
  calc
    _root_.MIPStarRE.QPBT.outcomeEventWeight S (.var (_root_.MIPStarRE.QPBT.msConstraintVars i 0)) (.constraint i)
        (fun _ b => _root_.MIPStarRE.QPBT.MagicSquareRigidity.ConstraintParityFailure i b) ≤
        _root_.MIPStarRE.QPBT.MagicSquareRigidity.rejectionMass S (.var (_root_.MIPStarRE.QPBT.msConstraintVars i 0)) (.constraint i) :=
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.outcome_event_weight_le_rejection_mass S _ _ _ (reverse_parity_failure_rejects i 0)
    _ ≤ 36 * ε :=
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.rejection_mass_le S ε hwin (_root_.MIPStarRE.QPBT.MagicSquareRigidity.ms_reverse_incidence_mem_support i 0)

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

section JointDefect







variable {G : _root_.MIPStarRE.QPBT.Game}











/-- Formalization-only: the identity as a spectral combination of the effects of
a measurement. -/
theorem smul_one_eq_sum_smul_effect {α d : Type} [Fintype α] [Fintype d]
    [DecidableEq d] (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α d) (s : ℂ) :
    s • (1 : _root_.LIDT.MIPStarRE.Quantum.Op d) = ∑ a, s • M.effect a := by
  rw [← Finset.smul_sum, M.sum_eq_one]

end JointDefect

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





section SignDefect

variable {G : _root_.MIPStarRE.QPBT.Game}





/-- Bob's sign observable deviates from a constant sign by at most twice the
square root of the mass of the answers carrying the other label. -/
theorem norm_bob_signObs_sub_const_sq_le (T : _root_.MIPStarRE.QPBT.Strategy G) (x : G.QuestionA)
    (y : G.QuestionB) (hA : _root_.MIPStarRE.QPBT.Measurement.IsProjective (T.A x))
    (hB : _root_.MIPStarRE.QPBT.Measurement.IsProjective (T.B y))
    (g : G.AnswerB → ZMod 2) (c : ZMod 2) :
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState (((_root_.MIPStarRE.QPBT.MagicSquareRigidity.bitSign c : ℝ) : ℂ) • (1 : _root_.LIDT.MIPStarRE.Quantum.Op (T.ιA × T.ιB)) -
        _root_.MIPStarRE.QPBT.heteroKron 1 (_root_.MIPStarRE.QPBT.MagicSquareRigidity.signObs (T.B y) g)) T.ψ‖ ^ 2 ≤
      4 * _root_.MIPStarRE.QPBT.bobEventWeight T y (fun b => c ≠ g b) := by
  classical
  have hconst : _root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.MagicSquareRigidity.signObs (T.A x) (fun _ => c)) (1 : _root_.LIDT.MIPStarRE.Quantum.Op T.ιB) =
      ((_root_.MIPStarRE.QPBT.MagicSquareRigidity.bitSign c : ℝ) : ℂ) • (1 : _root_.LIDT.MIPStarRE.Quantum.Op (T.ιA × T.ιB)) := by
    rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.signObs, ← _root_.MIPStarRE.QPBT.MagicSquareRigidity.smul_one_eq_sum_smul_effect (T.A x) (((_root_.MIPStarRE.QPBT.MagicSquareRigidity.bitSign c : ℝ) : ℂ)),
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.heteroKron_smul_left, _root_.MIPStarRE.QPBT.heteroKron_one_one]
  have h := _root_.MIPStarRE.QPBT.MagicSquareRigidity.norm_alice_sub_bob_signObs_sq_le T x y hA hB (fun _ => c) g
  rw [hconst] at h
  refine le_trans h (le_of_eq ?_)
  congr 1
  exact _root_.MIPStarRE.QPBT.outcome_event_weight_right_eq T x y (fun b => c ≠ g b)

end SignDefect

/-! ## Comparison of Born masses with the game error -/

/-- Formalization-only: a squared state-dependent bound by four times a mass
which is itself bounded by `36 * ε` yields closeness at scale `12 * sqrt ε`. -/
private theorem normCloseOn_of_sq_le {ι : Type} [Fintype ι] [DecidableEq ι]
    {ψ : EuclideanSpace ℂ ι} {M N : _root_.LIDT.MIPStarRE.Quantum.Op ι} {m ε : ℝ}
    (hsq : ‖_root_.MIPStarRE.QPBT.applyOperatorToState (M - N) ψ‖ ^ 2 ≤ 4 * m) (hm0 : 0 ≤ m)
    (hm : m ≤ 36 * ε) : _root_.MIPStarRE.QPBT.MagicSquareRigidity.NormCloseOn ψ (12 * Real.sqrt ε) M N := by
  have hε : (0 : ℝ) ≤ ε := by
    have h36 : (0 : ℝ) ≤ 36 * ε := le_trans hm0 hm
    linarith
  have hbound : ‖_root_.MIPStarRE.QPBT.applyOperatorToState (M - N) ψ‖ ^ 2 ≤ (12 * Real.sqrt ε) ^ 2 := by
    have hsq' : (12 * Real.sqrt ε) ^ 2 = 144 * ε := by
      rw [mul_pow, Real.sq_sqrt hε]
      ring
    rw [hsq']
    linarith
  calc ‖_root_.MIPStarRE.QPBT.applyOperatorToState (M - N) ψ‖
      = Real.sqrt (‖_root_.MIPStarRE.QPBT.applyOperatorToState (M - N) ψ‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((12 * Real.sqrt ε) ^ 2) := Real.sqrt_le_sqrt hbound
    _ = 12 * Real.sqrt ε := Real.sqrt_sq (by positivity)



/-- Formalization-only: monotonicity of Bob's marginal event mass. -/
private theorem bob_event_weight_mono (T : _root_.MIPStarRE.QPBT.Strategy _root_.MIPStarRE.QPBT.msGame) (y : _root_.MIPStarRE.QPBT.MsType)
    (E F : _root_.MIPStarRE.QPBT.MsAnswer → Prop) [DecidablePred E] [DecidablePred F]
    (h : ∀ b, E b → F b) : _root_.MIPStarRE.QPBT.bobEventWeight T y E ≤ _root_.MIPStarRE.QPBT.bobEventWeight T y F := by
  rw [← _root_.MIPStarRE.QPBT.outcome_event_weight_right_eq T y y E, ← _root_.MIPStarRE.QPBT.outcome_event_weight_right_eq T y y F]
  exact _root_.MIPStarRE.QPBT.outcome_event_weight_mono T y y _ _ fun _ b hb => h b hb

/-! ## The Magic Square reflections of the dilated strategy -/

































/-! ## The six row and column product relations -/







/-- The product of Bob's three cell reflections of a constraint question is the
reflection attached to the sum of the three reported bits. -/
theorem msCellObsB_prod (S : _root_.MIPStarRE.QPBT.Strategy _root_.MIPStarRE.QPBT.msGame) (i : Fin 6) :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.msCellObsB S i 0 * _root_.MIPStarRE.QPBT.MagicSquareRigidity.msCellObsB S i 1 * _root_.MIPStarRE.QPBT.MagicSquareRigidity.msCellObsB S i 2 =
      _root_.MIPStarRE.QPBT.heteroKron 1 (_root_.MIPStarRE.QPBT.MagicSquareRigidity.signObs ((_root_.MIPStarRE.QPBT.MagicSquareRigidity.msDilatedStrategy S).B (_root_.MIPStarRE.QPBT.MsType.constraint i))
        _root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitSum) := by
  rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.msCellObsB, _root_.MIPStarRE.QPBT.MagicSquareRigidity.msCellObsB, _root_.MIPStarRE.QPBT.MagicSquareRigidity.msCellObsB, _root_.MIPStarRE.QPBT.heteroKron_mul, _root_.MIPStarRE.QPBT.heteroKron_mul,
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.signObs_mul _ (_root_.MIPStarRE.QPBT.MagicSquareRigidity.msDilatedStrategy_isProjective_B S _),
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.signObs_mul _ (_root_.MIPStarRE.QPBT.MagicSquareRigidity.msDilatedStrategy_isProjective_B S _), mul_one, one_mul]
  rfl



/-- Formalization-only: nonnegativity of Bob's marginal event mass. -/
private theorem bob_event_weight_nonneg (T : _root_.MIPStarRE.QPBT.Strategy _root_.MIPStarRE.QPBT.msGame) (y : _root_.MIPStarRE.QPBT.MsType)
    (E : _root_.MIPStarRE.QPBT.MsAnswer → Prop) [DecidablePred E] : 0 ≤ _root_.MIPStarRE.QPBT.bobEventWeight T y E := by
  rw [← _root_.MIPStarRE.QPBT.outcome_event_weight_right_eq T y y E]
  exact _root_.MIPStarRE.QPBT.outcome_event_weight_nonneg T y y _





/-! ## Agreement of the two reflections attached to a common cell -/





/-! ## Permuted row and column products -/









/-! ## The two logical Pauli pairs -/

























/-! ## Unit scalars -/







/-! ## Building blocks of the solution-group computation -/







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

theorem solution (S : _root_.MIPStarRE.QPBT.Strategy _root_.MIPStarRE.QPBT.msGame) (ε : ℝ) (hwin : 1 - ε ≤ S.value)
    (i : Fin 6) :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.NormCloseOn (_root_.MIPStarRE.QPBT.MagicSquareRigidity.msDilatedStrategy S).ψ (12 * Real.sqrt ε)
      (((_root_.MIPStarRE.QPBT.MagicSquareRigidity.bitSign (_root_.MIPStarRE.QPBT.msParity i) : ℝ) : ℂ) • 1)
      (_root_.MIPStarRE.QPBT.MagicSquareRigidity.msCellObsB S i 0 * _root_.MIPStarRE.QPBT.MagicSquareRigidity.msCellObsB S i 1 * _root_.MIPStarRE.QPBT.MagicSquareRigidity.msCellObsB S i 2) := by
  classical
  have hsq := _root_.MIPStarRE.QPBT.MagicSquareRigidity.norm_bob_signObs_sub_const_sq_le (_root_.MIPStarRE.QPBT.MagicSquareRigidity.msDilatedStrategy S)
    (_root_.MIPStarRE.QPBT.MsType.constraint i) (_root_.MIPStarRE.QPBT.MsType.constraint i)
    (_root_.MIPStarRE.QPBT.MagicSquareRigidity.msDilatedStrategy_isProjective_A S _) (_root_.MIPStarRE.QPBT.MagicSquareRigidity.msDilatedStrategy_isProjective_B S _)
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitSum (_root_.MIPStarRE.QPBT.msParity i)
  rw [← _root_.MIPStarRE.QPBT.MagicSquareRigidity.msCellObsB_prod] at hsq
  refine normCloseOn_of_sq_le hsq (bob_event_weight_nonneg _ _ _) ?_
  calc _root_.MIPStarRE.QPBT.bobEventWeight (_root_.MIPStarRE.QPBT.MagicSquareRigidity.msDilatedStrategy S) (_root_.MIPStarRE.QPBT.MsType.constraint i)
        (fun b => _root_.MIPStarRE.QPBT.msParity i ≠ _root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitSum b)
      ≤ _root_.MIPStarRE.QPBT.bobEventWeight (_root_.MIPStarRE.QPBT.MagicSquareRigidity.msDilatedStrategy S) (_root_.MIPStarRE.QPBT.MsType.constraint i)
          (_root_.MIPStarRE.QPBT.MagicSquareRigidity.ConstraintParityFailure i) :=
        bob_event_weight_mono _ _ _ _ fun b hb =>
          _root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintParityFailure_of_bitSum_ne i b (Ne.symm hb)
    _ = _root_.MIPStarRE.QPBT.MagicSquareRigidity.bobParityFailureMass S i := _root_.MIPStarRE.QPBT.MagicSquareRigidity.ms_dilated_strategy_bob_parity_failure_mass S i
    _ ≤ 36 * ε := _root_.MIPStarRE.QPBT.MagicSquareRigidity.bob_parity_failure_mass_le S ε hwin i
