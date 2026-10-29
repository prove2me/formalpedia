-- Prove2me | solution 1 for MIPStarRE.QPBT.qBipartiteConsDefect_le_directRejectedMass
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:32:14.494975+00:00
-- url     : https://prove2.me/submissions/1066d527-2ed6-441d-80cc-5dca380e3fa3

-- Generated proof for MIPStarRE.QPBT.qBipartiteConsDefect_le_directRejectedMass.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_BranchComparison
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Strategy
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_StrategyClasses
import Mathlib
import Theorems.Thm_LIDT_MIPStarRE_LDT_PureState_ev_eq_re_inner
import Theorems.Thm_MIPStarRE_QPBT_outcomeWeight_sum_eq_one

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/DirectLowDegree/Transport/Strategy.lean. -/
/-!
# Strategy transport for the directly indexed low-degree game

This module reads one coordinate of a projective directly indexed strategy as
a two-space low individual degree test strategy.  The question and answer
transport of `Transport.Questions` supplies the canonical direct question of
every LDT line, with the reversed coordinate order and the leading index of
the decoded diagonal direction, together with answer readouts that are
covariant under line rebasing; this establishes all four covariance
conditions of `ProjStrat`.  The module also records exact Born-weight
formulas for both directions of strategy transport.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-458`
- `references/ldt-paper/test_definition.tex:49-151`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## From a direct strategy to an LDT strategy -/



























private theorem vectorBornAmplitude_add_left
    {iotaA iotaB : Type*}
    [Fintype iotaA] [DecidableEq iotaA]
    [Fintype iotaB] [DecidableEq iotaB]
    (psi : EuclideanSpace ℂ (iotaA × iotaB))
    (A₁ A₂ : _root_.LIDT.MIPStarRE.Quantum.Op iotaA) (B : _root_.LIDT.MIPStarRE.Quantum.Op iotaB) :
    vectorBornAmplitude psi (A₁ + A₂) B =
      vectorBornAmplitude psi A₁ B + vectorBornAmplitude psi A₂ B := by
  unfold vectorBornAmplitude _root_.MIPStarRE.QPBT.applyOperatorToState _root_.MIPStarRE.QPBT.heteroKron Matrix.kronecker
  rw [Matrix.add_kronecker]
  simp

private theorem vectorBornAmplitude_add_right
    {iotaA iotaB : Type*}
    [Fintype iotaA] [DecidableEq iotaA]
    [Fintype iotaB] [DecidableEq iotaB]
    (psi : EuclideanSpace ℂ (iotaA × iotaB))
    (A : _root_.LIDT.MIPStarRE.Quantum.Op iotaA) (B₁ B₂ : _root_.LIDT.MIPStarRE.Quantum.Op iotaB) :
    vectorBornAmplitude psi A (B₁ + B₂) =
      vectorBornAmplitude psi A B₁ + vectorBornAmplitude psi A B₂ := by
  unfold vectorBornAmplitude _root_.MIPStarRE.QPBT.applyOperatorToState _root_.MIPStarRE.QPBT.heteroKron Matrix.kronecker
  rw [Matrix.kronecker_add]
  simp

private theorem vectorBornAmplitude_zero_left
    {iotaA iotaB : Type*}
    [Fintype iotaA] [DecidableEq iotaA]
    [Fintype iotaB] [DecidableEq iotaB]
    (psi : EuclideanSpace ℂ (iotaA × iotaB)) (B : _root_.LIDT.MIPStarRE.Quantum.Op iotaB) :
    vectorBornAmplitude psi 0 B = 0 := by
  unfold vectorBornAmplitude _root_.MIPStarRE.QPBT.applyOperatorToState _root_.MIPStarRE.QPBT.heteroKron Matrix.kronecker
  rw [Matrix.zero_kronecker]
  simp

private theorem vectorBornAmplitude_zero_right
    {iotaA iotaB : Type*}
    [Fintype iotaA] [DecidableEq iotaA]
    [Fintype iotaB] [DecidableEq iotaB]
    (psi : EuclideanSpace ℂ (iotaA × iotaB)) (A : _root_.LIDT.MIPStarRE.Quantum.Op iotaA) :
    vectorBornAmplitude psi A 0 = 0 := by
  unfold vectorBornAmplitude _root_.MIPStarRE.QPBT.applyOperatorToState _root_.MIPStarRE.QPBT.heteroKron Matrix.kronecker
  rw [Matrix.kronecker_zero]
  simp

private theorem vectorBornWeight_add_left
    {iotaA iotaB : Type*}
    [Fintype iotaA] [DecidableEq iotaA]
    [Fintype iotaB] [DecidableEq iotaB]
    (psi : EuclideanSpace ℂ (iotaA × iotaB))
    (A₁ A₂ : _root_.LIDT.MIPStarRE.Quantum.Op iotaA) (B : _root_.LIDT.MIPStarRE.Quantum.Op iotaB) :
    vectorBornWeight psi (A₁ + A₂) B =
      vectorBornWeight psi A₁ B + vectorBornWeight psi A₂ B := by
  unfold vectorBornWeight
  rw [vectorBornAmplitude_add_left, Complex.add_re]

private theorem vectorBornWeight_add_right
    {iotaA iotaB : Type*}
    [Fintype iotaA] [DecidableEq iotaA]
    [Fintype iotaB] [DecidableEq iotaB]
    (psi : EuclideanSpace ℂ (iotaA × iotaB))
    (A : _root_.LIDT.MIPStarRE.Quantum.Op iotaA) (B₁ B₂ : _root_.LIDT.MIPStarRE.Quantum.Op iotaB) :
    vectorBornWeight psi A (B₁ + B₂) =
      vectorBornWeight psi A B₁ + vectorBornWeight psi A B₂ := by
  unfold vectorBornWeight
  rw [vectorBornAmplitude_add_right, Complex.add_re]

private theorem vectorBornWeight_finset_sum_left
    {alpha iotaA iotaB : Type*}
    [Fintype iotaA] [DecidableEq iotaA]
    [Fintype iotaB] [DecidableEq iotaB]
    (psi : EuclideanSpace ℂ (iotaA × iotaB))
    (s : Finset alpha) (A : alpha → _root_.LIDT.MIPStarRE.Quantum.Op iotaA) (B : _root_.LIDT.MIPStarRE.Quantum.Op iotaB) :
    vectorBornWeight psi (∑ a ∈ s, A a) B =
      ∑ a ∈ s, vectorBornWeight psi (A a) B := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [vectorBornWeight, vectorBornAmplitude_zero_left]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        vectorBornWeight_add_left, ih]

private theorem vectorBornWeight_finset_sum_right
    {beta iotaA iotaB : Type*}
    [Fintype iotaA] [DecidableEq iotaA]
    [Fintype iotaB] [DecidableEq iotaB]
    (psi : EuclideanSpace ℂ (iotaA × iotaB))
    (A : _root_.LIDT.MIPStarRE.Quantum.Op iotaA) (s : Finset beta) (B : beta → _root_.LIDT.MIPStarRE.Quantum.Op iotaB) :
    vectorBornWeight psi A (∑ b ∈ s, B b) =
      ∑ b ∈ s, vectorBornWeight psi A (B b) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [vectorBornWeight, vectorBornAmplitude_zero_right]
  | @insert b s hb ih =>
      rw [Finset.sum_insert hb, Finset.sum_insert hb,
        vectorBornWeight_add_right, ih]

/-- Expectations in the density state associated with a strategy agree with
the strategy's vector Born quadratic form. -/
private theorem strategyQuantumState_ev_eq_vectorBornWeight
    {G : _root_.MIPStarRE.QPBT.Game} (S : _root_.MIPStarRE.QPBT.Strategy G) (A : _root_.LIDT.MIPStarRE.Quantum.Op S.ιA) (B : _root_.LIDT.MIPStarRE.Quantum.Op S.ιB) :
    _root_.LIDT.MIPStarRE.LDT.ev (_root_.MIPStarRE.QPBT.strategyQuantumState S) (_root_.LIDT.MIPStarRE.LDT.opTensor A B) =
      vectorBornWeight S.ψ A B := by
  letI : Nonempty (S.ιA × S.ιB) := strategy_carrier_nonempty S
  rw [show _root_.MIPStarRE.QPBT.strategyQuantumState S =
      _root_.LIDT.MIPStarRE.LDT.PureState.toQuantumState (_root_.MIPStarRE.QPBT.strategyPureState S) by
        simp [_root_.MIPStarRE.QPBT.strategyQuantumState],
    _root_.LIDT.MIPStarRE.LDT.PureState.ev_eq_re_inner]
  unfold vectorBornWeight vectorBornAmplitude _root_.MIPStarRE.QPBT.applyOperatorToState _root_.MIPStarRE.QPBT.heteroKron _root_.LIDT.MIPStarRE.LDT.opTensor
  simp_rw [EuclideanSpace.inner_eq_star_dotProduct]
  change (star S.ψ ⬝ᵥ
      (Matrix.kronecker A B *ᵥ S.ψ)).re =
    ((Matrix.kronecker A B *ᵥ S.ψ) ⬝ᵥ star S.ψ).re
  rw [dotProduct_comm]

/-- Postprocessing both local measurements gives the exact double sum of the
original Born weights over the two answer fibers. -/
theorem directPostprocessBornWeight
    (D : _root_.MIPStarRE.QPBT.DirectLdParams) (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.directLdGame D))
    (hS : S.IsProjective)
    {alpha beta : Type*} [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    (x y : _root_.MIPStarRE.QPBT.DirectLdQuestion D)
    (readA : _root_.MIPStarRE.QPBT.DirectLdAnswer D → alpha)
    (readB : _root_.MIPStarRE.QPBT.DirectLdAnswer D → beta)
    (a : alpha) (b : beta) :
    _root_.LIDT.MIPStarRE.LDT.ev (_root_.MIPStarRE.QPBT.strategyQuantumState S)
        (_root_.LIDT.MIPStarRE.LDT.opTensor
          ((_root_.LIDT.MIPStarRE.LDT.ProjMeas.postprocess
            (_root_.MIPStarRE.QPBT.matrixMeasurementToLDTProjMeas (S.A x) (hS.1 x)) readA).outcome a)
          ((_root_.LIDT.MIPStarRE.LDT.ProjMeas.postprocess
            (_root_.MIPStarRE.QPBT.matrixMeasurementToLDTProjMeas (S.B y) (hS.2 y)) readB).outcome b)) =
      ∑ directA ∈ Finset.univ.filter (fun answer => readA answer = a),
        ∑ directB ∈ Finset.univ.filter (fun answer => readB answer = b),
          _root_.MIPStarRE.QPBT.outcomeWeight S x y directA directB := by
  rw [strategyQuantumState_ev_eq_vectorBornWeight]
  simp only [_root_.LIDT.MIPStarRE.LDT.ProjMeas.postprocess, _root_.LIDT.MIPStarRE.LDT.SubMeas.postprocess_outcome,
    _root_.MIPStarRE.QPBT.matrixMeasurementToLDTProjMeas_outcome]
  rw [vectorBornWeight_finset_sum_left]
  apply Finset.sum_congr rfl
  intro directA _
  rw [vectorBornWeight_finset_sum_right]
  rfl















end

end MIPStarRE.QPBT

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

/- Source helpers from QPBT/Combining/DirectLowDegree/Transport/BranchComparison.lean. -/
/-!
# Branch comparison for the coordinate strategies of the direct low-degree game

Every branch of the low individual degree failure probability of a coordinate
strategy `directCoordinateProjStrat` is compared with the ordered type-pair
branch of the direct game asking the same questions.  An accepted direct
answer pair reads out to equal LDT answers: the line answer, rebased to the
LDT line and evaluated at the LDT base point, is the point answer, and the
zero-direction convention reads the constant value at the base point.  Hence
the LDT inconsistency mass at a question pair is at most the rejected direct
Born mass there.  The point-agreement and axis-line branches then compare
exactly after the coordinate reindexing of `directPointEquiv`; the diagonal
branches are treated in `Transport.DiagonalRecursion`.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:214-458`
- `references/ldt-paper/test_definition.tex:130-151`
- Blueprint `def:ld-question-distribution`, `lem:ld-aline-level`,
  `lem:ld-dline-level`, `lem:ld-question-typed-cl`, `lem:alnf`, `lem:dlnf`,
  `def:ld-win-predicate`, `rem:ld-win-zero-direction`, and `def:ld-meas`
- `MIPStarRE/LDT/Test/StrategyFailures.lean:18-130`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.Quantum

noncomputable section



/-! ## Rejected Born mass at a fixed question pair -/



theorem directRejectedMass_nonneg (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.directLdGame D)) (x y : _root_.MIPStarRE.QPBT.DirectLdQuestion D) :
    0 ≤ _root_.MIPStarRE.QPBT.directRejectedMass D S x y := by
  refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
  split_ifs
  · exact le_rfl
  · exact _root_.MIPStarRE.QPBT.outcomeWeight_nonneg S x y a b





/-! ## Accepted answer pairs read out consistently

An accepted answer pair of the direct game consists of well-formed answers
satisfying the line-versus-point clause or the consistency clause of
`def:ld-win-predicate`.  The readouts of `Transport.Questions` evaluate the
rebased line polynomial at the LDT base point, which is the direct point
at the canonical rebase parameter; the accepted clause forces this value to
be the point answer.  Zero directions use the constant readout at the base
point, where the universal clause of `rem:ld-win-zero-direction` gives the
value at parameter zero. -/















/-! ## Direct samples as products -/



/-! ## The point-agreement and axis-line branches -/



end

end MIPStarRE.QPBT

/-!
# Branch comparison for the coordinate strategies of the direct low-degree game

Every branch of the low individual degree failure probability of a coordinate
strategy `directCoordinateProjStrat` is compared with the ordered type-pair
branch of the direct game asking the same questions.  An accepted direct
answer pair reads out to equal LDT answers: the line answer, rebased to the
LDT line and evaluated at the LDT base point, is the point answer, and the
zero-direction convention reads the constant value at the base point.  Hence
the LDT inconsistency mass at a question pair is at most the rejected direct
Born mass there.  The point-agreement and axis-line branches then compare
exactly after the coordinate reindexing of `directPointEquiv`; the diagonal
branches are treated in `Transport.DiagonalRecursion`.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:214-458`
- `references/ldt-paper/test_definition.tex:130-151`
- Blueprint `def:ld-question-distribution`, `lem:ld-aline-level`,
  `lem:ld-dline-level`, `lem:ld-question-typed-cl`, `lem:alnf`, `lem:dlnf`,
  `def:ld-win-predicate`, `rem:ld-win-zero-direction`, and `def:ld-meas`
- `MIPStarRE/LDT/Test/StrategyFailures.lean:18-130`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/



open scoped BigOperators MatrixOrder Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.Quantum





/-! ## Rejected Born mass at a fixed question pair -/

theorem solution
    (D : _root_.MIPStarRE.QPBT.DirectLdParams) (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.directLdGame D))
    (hS : S.IsProjective)
    {Outcome : Type*} [Fintype Outcome]
    (x y : _root_.MIPStarRE.QPBT.DirectLdQuestion D)
    (readA readB : _root_.MIPStarRE.QPBT.DirectLdAnswer D → Outcome)
    (hwin : ∀ a b, _root_.MIPStarRE.QPBT.directLdWinPredicate D x y a b = true → readA a = readB b) :
    _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect (_root_.MIPStarRE.QPBT.strategyQuantumState S)
        (_root_.LIDT.MIPStarRE.LDT.ProjMeas.postprocess
          (_root_.MIPStarRE.QPBT.matrixMeasurementToLDTProjMeas (S.A x) (hS.1 x)) readA).toSubMeas
        (_root_.LIDT.MIPStarRE.LDT.ProjMeas.postprocess
          (_root_.MIPStarRE.QPBT.matrixMeasurementToLDTProjMeas (S.B y) (hS.2 y)) readB).toSubMeas ≤
      _root_.MIPStarRE.QPBT.directRejectedMass D S x y := by
  classical
  have hmatch :
      _root_.LIDT.MIPStarRE.LDT.qBipartiteMatchMass (_root_.MIPStarRE.QPBT.strategyQuantumState S)
          (_root_.LIDT.MIPStarRE.LDT.ProjMeas.postprocess
            (_root_.MIPStarRE.QPBT.matrixMeasurementToLDTProjMeas (S.A x) (hS.1 x)) readA).toSubMeas
          (_root_.LIDT.MIPStarRE.LDT.ProjMeas.postprocess
            (_root_.MIPStarRE.QPBT.matrixMeasurementToLDTProjMeas (S.B y) (hS.2 y)) readB).toSubMeas =
        ∑ a : _root_.MIPStarRE.QPBT.DirectLdAnswer D, ∑ b : _root_.MIPStarRE.QPBT.DirectLdAnswer D,
          if readA a = readB b then _root_.MIPStarRE.QPBT.outcomeWeight S x y a b else 0 := by
    unfold _root_.LIDT.MIPStarRE.LDT.qBipartiteMatchMass
    calc
      ∑ c : Outcome, _root_.LIDT.MIPStarRE.LDT.ev (_root_.MIPStarRE.QPBT.strategyQuantumState S)
          (_root_.LIDT.MIPStarRE.LDT.opTensor
            ((_root_.LIDT.MIPStarRE.LDT.ProjMeas.postprocess
              (_root_.MIPStarRE.QPBT.matrixMeasurementToLDTProjMeas (S.A x) (hS.1 x)) readA).outcome c)
            ((_root_.LIDT.MIPStarRE.LDT.ProjMeas.postprocess
              (_root_.MIPStarRE.QPBT.matrixMeasurementToLDTProjMeas (S.B y) (hS.2 y)) readB).outcome c)) =
          ∑ c : Outcome,
            ∑ a ∈ Finset.univ.filter (fun a => readA a = c),
              ∑ b ∈ Finset.univ.filter (fun b => readB b = c),
                _root_.MIPStarRE.QPBT.outcomeWeight S x y a b := by
        refine Finset.sum_congr rfl ?_
        intro c _
        exact _root_.MIPStarRE.QPBT.directPostprocessBornWeight D S hS x y readA readB c c
      _ = ∑ c : Outcome, ∑ a : _root_.MIPStarRE.QPBT.DirectLdAnswer D,
            if readA a = c then
              ∑ b : _root_.MIPStarRE.QPBT.DirectLdAnswer D,
                if readB b = c then _root_.MIPStarRE.QPBT.outcomeWeight S x y a b else 0
            else 0 := by
        simp only [Finset.sum_filter]
      _ = ∑ a : _root_.MIPStarRE.QPBT.DirectLdAnswer D, ∑ c : Outcome,
            if readA a = c then
              ∑ b : _root_.MIPStarRE.QPBT.DirectLdAnswer D,
                if readB b = c then _root_.MIPStarRE.QPBT.outcomeWeight S x y a b else 0
            else 0 := Finset.sum_comm
      _ = ∑ a : _root_.MIPStarRE.QPBT.DirectLdAnswer D, ∑ b : _root_.MIPStarRE.QPBT.DirectLdAnswer D,
            if readA a = readB b then _root_.MIPStarRE.QPBT.outcomeWeight S x y a b else 0 := by
        refine Finset.sum_congr rfl ?_
        intro a _
        rw [Finset.sum_ite_eq]
        simp only [Finset.mem_univ, if_true]
        refine Finset.sum_congr rfl ?_
        intro b _
        by_cases hab : readA a = readB b
        · simp [hab]
        · have hba : ¬ readB b = readA a := fun h => hab h.symm
          simp [hab, hba]
  have hone : ∑ a : _root_.MIPStarRE.QPBT.DirectLdAnswer D, ∑ b : _root_.MIPStarRE.QPBT.DirectLdAnswer D,
      _root_.MIPStarRE.QPBT.outcomeWeight S x y a b = 1 :=
    _root_.MIPStarRE.QPBT.outcomeWeight_sum_eq_one S x y
  have htotal :
      _root_.LIDT.MIPStarRE.LDT.ev (_root_.MIPStarRE.QPBT.strategyQuantumState S)
        (_root_.LIDT.MIPStarRE.LDT.opTensor
          (_root_.LIDT.MIPStarRE.LDT.ProjMeas.postprocess
            (_root_.MIPStarRE.QPBT.matrixMeasurementToLDTProjMeas (S.A x) (hS.1 x)) readA).toSubMeas.total
          (_root_.LIDT.MIPStarRE.LDT.ProjMeas.postprocess
            (_root_.MIPStarRE.QPBT.matrixMeasurementToLDTProjMeas (S.B y) (hS.2 y)) readB).toSubMeas.total) =
        1 := by
    change _root_.LIDT.MIPStarRE.LDT.ev (_root_.MIPStarRE.QPBT.strategyQuantumState S)
      (Matrix.kroneckerMap (fun x1 x2 => x1 * x2) (1 : _root_.LIDT.MIPStarRE.Quantum.Op S.ιA) (1 : _root_.LIDT.MIPStarRE.Quantum.Op S.ιB)) = 1
    rw [Matrix.one_kronecker_one]
    exact _root_.LIDT.MIPStarRE.LDT.ev_one_of_isNormalized _ (_root_.MIPStarRE.QPBT.strategyQuantumState_isNormalized S)
  simp only [_root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect]
  refine max_le (_root_.MIPStarRE.QPBT.directRejectedMass_nonneg D S x y) ?_
  rw [htotal, hmatch, ← hone, ← Finset.sum_sub_distrib]
  unfold _root_.MIPStarRE.QPBT.directRejectedMass
  refine Finset.sum_le_sum fun a _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun b _ => ?_
  have hw := _root_.MIPStarRE.QPBT.outcomeWeight_nonneg S x y a b
  by_cases hacc : _root_.MIPStarRE.QPBT.directLdWinPredicate D x y a b = true
  · have hread := hwin a b hacc
    simp [hacc, hread]
  · rw [if_neg hacc]
    split_ifs <;> linarith
