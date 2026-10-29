-- Prove2me | solution 1 for MIPStarRE.QPBT.MagicSquareRigidity.msCellObsA_close_msVarObsB
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:41:35.233139+00:00
-- url     : https://prove2.me/submissions/86b03d62-1032-405b-9f13-a9443b5b9515

-- Generated proof for MIPStarRE.QPBT.MagicSquareRigidity.msCellObsA_close_msVarObsB.
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
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_CellRelations
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Dilation
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Reflections
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Relations
import Theorems.Thm_MIPStarRE_QPBT_MagicSquareRigidity_naimarkCompression_naimarkDilatedEffect
import Theorems.Thm_MIPStarRE_QPBT_MagicSquareRigidity_naimarkDilatedEffect_isProj
import Theorems.Thm_MIPStarRE_QPBT_MagicSquareRigidity_norm_alice_sub_bob_signObs_sq_le
import Theorems.Thm_MIPStarRE_QPBT_MagicSquareRigidity_rejection_mass_le_thirty_six_mul_total
import Theorems.Thm_MIPStarRE_QPBT_MagicSquareRigidity_total_rejection_mass_eq_one_sub_value
import Theorems.Thm_MIPStarRE_QPBT_outcome_event_weight_mono

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





/-! ## The Magic Square reflections of the dilated strategy -/

































/-! ## The six row and column product relations -/

















/-! ## Agreement of the two reflections attached to a common cell -/





/-! ## Permuted row and column products -/









/-! ## The two logical Pauli pairs -/

























/-! ## Unit scalars -/







/-! ## Building blocks of the solution-group computation -/







end

end MIPStarRE.QPBT.MagicSquareRigidity

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





/-- The dilation preserves the mass of every answer event. -/
theorem ms_dilated_strategy_outcome_event_weight (S : _root_.MIPStarRE.QPBT.Strategy _root_.MIPStarRE.QPBT.msGame) (x y : _root_.MIPStarRE.QPBT.MsType)
    (E : _root_.MIPStarRE.QPBT.MsAnswer → _root_.MIPStarRE.QPBT.MsAnswer → Prop) [DecidableRel E] :
    _root_.MIPStarRE.QPBT.outcomeEventWeight (_root_.MIPStarRE.QPBT.MagicSquareRigidity.msDilatedStrategy S) x y E = _root_.MIPStarRE.QPBT.outcomeEventWeight S x y E := by
  unfold _root_.MIPStarRE.QPBT.outcomeEventWeight
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
    by_cases h : E a b <;> simp [h, _root_.MIPStarRE.QPBT.MagicSquareRigidity.ms_dilated_strategy_outcome_weight]



















/-- The dilation preserves the forward cell-consistency defect. -/
theorem ms_dilated_strategy_forward_cell_mismatch_mass (S : _root_.MIPStarRE.QPBT.Strategy _root_.MIPStarRE.QPBT.msGame)
    (i : Fin 6) (k : Fin 3) :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.forwardCellMismatchMass (_root_.MIPStarRE.QPBT.MagicSquareRigidity.msDilatedStrategy S) i k = _root_.MIPStarRE.QPBT.MagicSquareRigidity.forwardCellMismatchMass S i k :=
  _root_.MIPStarRE.QPBT.MagicSquareRigidity.ms_dilated_strategy_outcome_event_weight S _ _ _







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







/-- A constraint-to-variable incidence belongs to the question support. -/
theorem ms_forward_incidence_mem_support (i : Fin 6) (k : Fin 3) :
    (.constraint i, .var (_root_.MIPStarRE.QPBT.msConstraintVars i k)) ∈
      (_root_.MIPStarRE.QPBT.graphDistribution _root_.MIPStarRE.QPBT.msEdges _root_.MIPStarRE.QPBT.msEdges_nonempty).support := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
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



















/-- The three cells in any fixed row or column are distinct. -/
theorem constraint_vars_injective (i : Fin 6) : Function.Injective (_root_.MIPStarRE.QPBT.msConstraintVars i) := by
  intro k l hkl
  apply Fin.ext
  unfold _root_.MIPStarRE.QPBT.msConstraintVars at hkl
  split at hkl <;> simp only [Fin.mk.injEq] at hkl ⊢ <;> omega



























private theorem forward_cell_mismatch_rejects (i : Fin 6) (k : Fin 3)
    (a b : _root_.MIPStarRE.QPBT.MsAnswer) (hmismatch : _root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitOrZero k a ≠ _root_.MIPStarRE.QPBT.msBitOrZero b) :
    _root_.MIPStarRE.QPBT.msWinPredicate (.constraint i) (.var (_root_.MIPStarRE.QPBT.msConstraintVars i k)) a b = false := by
  cases a with
  | bit γa => rfl
  | triple β =>
      cases b with
      | triple βb => rfl
      | bit γ =>
          simp only [_root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitOrZero, _root_.MIPStarRE.QPBT.msBitOrZero] at hmismatch
          rw [_root_.MIPStarRE.QPBT.msWinPredicate, decide_eq_false_iff_not]
          intro haccept
          rcases haccept.2 with ⟨l, hl, hbit⟩
          have hlk : l = k := _root_.MIPStarRE.QPBT.MagicSquareRigidity.constraint_vars_injective i hl
          subst l
          exact hmismatch hbit



/-- Every forward directed incidence has cell-mismatch mass at most `36 * ε`. -/
theorem forward_cell_mismatch_mass_le (S : _root_.MIPStarRE.QPBT.Strategy _root_.MIPStarRE.QPBT.msGame) (ε : ℝ)
    (hwin : 1 - ε ≤ S.value) (i : Fin 6) (k : Fin 3) :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.forwardCellMismatchMass S i k ≤ 36 * ε := by
  unfold _root_.MIPStarRE.QPBT.MagicSquareRigidity.forwardCellMismatchMass
  calc
    _root_.MIPStarRE.QPBT.outcomeEventWeight S (.constraint i) (.var (_root_.MIPStarRE.QPBT.msConstraintVars i k))
        (fun a b => _root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitOrZero k a ≠ _root_.MIPStarRE.QPBT.msBitOrZero b) ≤
        _root_.MIPStarRE.QPBT.MagicSquareRigidity.rejectionMass S (.constraint i) (.var (_root_.MIPStarRE.QPBT.msConstraintVars i k)) :=
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.outcome_event_weight_le_rejection_mass S _ _ _ (forward_cell_mismatch_rejects i k)
    _ ≤ 36 * ε :=
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.rejection_mass_le S ε hwin (_root_.MIPStarRE.QPBT.MagicSquareRigidity.ms_forward_incidence_mem_support i k)



/-! ## Row and column parity products -/





































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

theorem solution (S : _root_.MIPStarRE.QPBT.Strategy _root_.MIPStarRE.QPBT.msGame) (ε : ℝ)
    (hwin : 1 - ε ≤ S.value) (i : Fin 6) (k : Fin 3) :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.NormCloseOn (_root_.MIPStarRE.QPBT.MagicSquareRigidity.msDilatedStrategy S).ψ (12 * Real.sqrt ε) (_root_.MIPStarRE.QPBT.MagicSquareRigidity.msCellObsA S i k)
      (_root_.MIPStarRE.QPBT.MagicSquareRigidity.msVarObsB S (_root_.MIPStarRE.QPBT.msConstraintVars i k)) := by
  classical
  have hsq := _root_.MIPStarRE.QPBT.MagicSquareRigidity.norm_alice_sub_bob_signObs_sq_le (_root_.MIPStarRE.QPBT.MagicSquareRigidity.msDilatedStrategy S)
    (_root_.MIPStarRE.QPBT.MsType.constraint i) (_root_.MIPStarRE.QPBT.MsType.var (_root_.MIPStarRE.QPBT.msConstraintVars i k))
    (_root_.MIPStarRE.QPBT.MagicSquareRigidity.msDilatedStrategy_isProjective_A S _) (_root_.MIPStarRE.QPBT.MagicSquareRigidity.msDilatedStrategy_isProjective_B S _)
    (_root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitOrZero k) _root_.MIPStarRE.QPBT.msBitOrZero
  refine normCloseOn_of_sq_le hsq (_root_.MIPStarRE.QPBT.outcome_event_weight_nonneg _ _ _ _) ?_
  calc _root_.MIPStarRE.QPBT.outcomeEventWeight (_root_.MIPStarRE.QPBT.MagicSquareRigidity.msDilatedStrategy S) (_root_.MIPStarRE.QPBT.MsType.constraint i)
        (_root_.MIPStarRE.QPBT.MsType.var (_root_.MIPStarRE.QPBT.msConstraintVars i k))
        (fun a b => _root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitOrZero k a ≠ _root_.MIPStarRE.QPBT.msBitOrZero b)
      = _root_.MIPStarRE.QPBT.MagicSquareRigidity.forwardCellMismatchMass S i k :=
        _root_.MIPStarRE.QPBT.MagicSquareRigidity.ms_dilated_strategy_forward_cell_mismatch_mass S i k
    _ ≤ 36 * ε := _root_.MIPStarRE.QPBT.MagicSquareRigidity.forward_cell_mismatch_mass_le S ε hwin i k
