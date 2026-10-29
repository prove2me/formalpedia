-- Prove2me | solution 1 for MIPStarRE.QPBT.ExtendedLineGame.strategy_value_ge_directPassingErrorEnvelope
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T02:49:35.809221+00:00
-- url     : https://prove2.me/submissions/4dc96a15-133c-425d-a889-d9eaa0269779

-- Generated proof for MIPStarRE.QPBT.ExtendedLineGame.strategy_value_ge_directPassingErrorEnvelope.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
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
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_GameValue
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame
import Definitions.Def_QPBT_QPBT_Combining_PassingError
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_completedLinePointDefect_aaBa_nonneg
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_mixed_branch_rejection_eq_zero
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_seven_branch_rejections_le
import Theorems.Thm_MIPStarRE_QPBT_directLdRejectionProbability_eq_one_sub_value

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.ExtendedLineGame
end MIPStarRE.QPBT.ExtendedLineGame
namespace MIPStarRE.QPBT.Strategy
end MIPStarRE.QPBT.Strategy

/- Source helpers from QPBT/Combining/DirectLowDegree/GameValue.lean. -/
/-!
# Rejection probabilities for the directly indexed low-degree game

This module compares the rejection probability of the directly indexed game
with the branch weights used by the low individual degree test.
All declarations below are formalization-only support derived from the game
value; none is a paper-labelled result.

## References

The uniform distribution on the three ordered question types is specified in
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:178-186`,
and its verifier is specified in the same file at lines 320-392.  The three
equal outer weights of the low individual degree test and its uniform role
choices are specified in `references/ldt-paper/test_definition.tex:10-67`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.Quantum

noncomputable section









/-- Formalization-only expansion of a sum over the three low-degree question
types, in point, axis-line, and diagonal-line order.  This supports the uniform
branch calculation for the game in
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:178-186`. -/
theorem sum_ldType (f : _root_.MIPStarRE.QPBT.LdType → ℝ) :
    ∑ t : _root_.MIPStarRE.QPBT.LdType, f t = f .point + f .aline + f .dline := by
  change (Finset.univ : Finset _root_.MIPStarRE.QPBT.LdType).sum f = _
  rw [show (Finset.univ : Finset _root_.MIPStarRE.QPBT.LdType) = {.point, .aline, .dline} by decide]
  simp [add_assoc]

/-- The uniform average over the nine ordered pairs of low-degree question
types is the arithmetic mean of the nine values.  Both the directly indexed
game with the original parameters and the one with the combined parameters
weight their ordered type pairs uniformly, so the assembly of
`lem:ld-combined-value` sums its nine branch-wise bounds through this
identity. -/
theorem avgOver_ldType_pair (f : _root_.MIPStarRE.QPBT.LdType × _root_.MIPStarRE.QPBT.LdType → ℝ) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.LdType × _root_.MIPStarRE.QPBT.LdType)) f =
      (f (.point, .point) + f (.point, .aline) + f (.point, .dline) +
        (f (.aline, .point) + f (.aline, .aline) + f (.aline, .dline)) +
        (f (.dline, .point) + f (.dline, .aline) + f (.dline, .dline))) / 9 := by
  unfold _root_.LIDT.MIPStarRE.LDT.avgOver _root_.LIDT.MIPStarRE.LDT.uniformDistribution _root_.LIDT.MIPStarRE.LDT.Distribution.uniformOnFinset
  simp only [Finset.mem_univ, if_true, Finset.card_univ, Fintype.card_prod]
  rw [show Fintype.card _root_.MIPStarRE.QPBT.LdType = 3 by decide]
  rw [Fintype.sum_prod_type]
  simp_rw [_root_.MIPStarRE.QPBT.sum_ldType]
  ring









end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/PassingError.lean. -/
/-! # Capped scalar envelope for direct-game error bounds

This module gives a concrete polynomial envelope for a scalar expression assembled from
seven prospective rejection bounds in the directly indexed extended-line game. It is a
formalization-only arithmetic auxiliary: it does not prove that any game branch satisfies
one of these bounds, nor does it prove a passing-value theorem.

The cap by one records the independent fact that a rejection probability is at most one.
It is essential for the polynomial-error contract: the uncapped function
`2 * x + Real.sqrt x + y` cannot be bounded by one positive power of `x` both near zero
and at infinity.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`
- Parent issue Dengnifer/MIPStarRE-QPBT-bak#119 and arithmetic issue
  Dengnifer/MIPStarRE-QPBT-bak#326
-/

@[expose] public section

namespace MIPStarRE.QPBT







/-- The proposed seven-term scalar error is bounded by nine times the uncapped
linear-square-root expression. The variables are only nonnegative real numbers here;
no game-level branch estimate is asserted. -/
theorem seven_branch_scalar_error_le (Q L r : ℝ) (hQ : 0 ≤ Q) (hL : 0 ≤ L)
    (hr : 0 ≤ r) :
    Q + 16 * L + 4 * Real.sqrt (Q + 2 * L) + 5 * r ≤
      9 * (2 * (Q + L) + Real.sqrt (Q + L) + r) := by
  have hQL : 0 ≤ Q + L := by linarith
  have hQ2L : 0 ≤ Q + 2 * L := by linarith
  have hroot : Real.sqrt (Q + 2 * L) ≤ 2 * Real.sqrt (Q + L) := by
    nlinarith [Real.sq_sqrt hQL, Real.sq_sqrt hQ2L,
      Real.sqrt_nonneg (Q + L), Real.sqrt_nonneg (Q + 2 * L)]
  nlinarith [Real.sqrt_nonneg (Q + L)]

private theorem min_linear_sqrt_le_directPassingErrorEnvelope (x y : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    min 1 (2 * x + Real.sqrt x + y) ≤ _root_.MIPStarRE.QPBT.directPassingErrorEnvelope x y := by
  by_cases hxOne : x ≤ 1
  · have hsqrtOne : Real.sqrt x ≤ 1 := by
      simpa using Real.sqrt_le_sqrt hxOne
    have hxSqrt : x ≤ Real.sqrt x := by
      nlinarith [Real.sq_sqrt hx, Real.sqrt_nonneg x]
    exact (min_le_right _ _).trans (by
      dsimp [_root_.MIPStarRE.QPBT.directPassingErrorEnvelope]
      nlinarith)
  · have hsqrtOne : 1 ≤ Real.sqrt x := by
      have hxOne' : 1 ≤ x := le_of_not_ge hxOne
      simpa using Real.sqrt_le_sqrt hxOne'
    exact (min_le_left _ _).trans (by
      dsimp [_root_.MIPStarRE.QPBT.directPassingErrorEnvelope]
      nlinarith [Real.sqrt_nonneg x])

/-- After averaging the seven scalar contributions by the nine equally weighted game
branches and applying the probability cap, the result is bounded by the concrete
polynomial envelope. This theorem assumes only the displayed nonnegative scalar inputs;
it does not establish the unfinished branch bounds that would supply them. -/
theorem seven_branch_capped_error_le_directPassingErrorEnvelope
    (Q L r : ℝ) (hQ : 0 ≤ Q) (hL : 0 ≤ L) (hr : 0 ≤ r) :
    min 1 ((Q + 16 * L + 4 * Real.sqrt (Q + 2 * L) + 5 * r) / 9) ≤
      _root_.MIPStarRE.QPBT.directPassingErrorEnvelope (Q + L) r := by
  have hraw := _root_.MIPStarRE.QPBT.seven_branch_scalar_error_le Q L r hQ hL hr
  have hdiv :
      (Q + 16 * L + 4 * Real.sqrt (Q + 2 * L) + 5 * r) / 9 ≤
        2 * (Q + L) + Real.sqrt (Q + L) + r := by
    nlinarith
  exact (min_le_min_left 1 hdiv).trans
    (min_linear_sqrt_le_directPassingErrorEnvelope (Q + L) r (by linarith) hr)

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

/- Source helpers from QPBT/Games/DistanceTheorems/Support.lean. -/
/-!
# Finite-dimensional operator estimates for state-dependent distance

This module contains finite-dimensional operator and finite-sum identities used
by the paper-facing distance theorems. It introduces no new mathematical
assumptions or source-facing statements.

## References

- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-395`
- `references/ldt-paper/preliminaries.tex:649-666`
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.DistanceCalculus

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective





























































/-- Formalization-only auxiliary lemma for the agreement facts (Facts 4.13 and
4.14), item 2: state-dependent squared distance between operator families is
nonnegative. -/
theorem opFamilyDistSq_nonneg {X α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (M N : X → α → _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (ψ : EuclideanSpace ℂ ι) :
    0 ≤ _root_.MIPStarRE.QPBT.opFamilyDistSq μ M N ψ := by
  unfold _root_.MIPStarRE.QPBT.opFamilyDistSq _root_.LIDT.MIPStarRE.LDT.avgOver
  exact Finset.sum_nonneg fun x _ => mul_nonneg (μ.nonnegative x)
    (Finset.sum_nonneg fun a _ => sq_nonneg _)





























end MIPStarRE.QPBT.DistanceCalculus

/- Source helpers from QPBT/Combining/DirectLowDegree/RejectionBounds.lean. -/
/-! # Probability bounds for the directly indexed low-degree game

This module records two elementary probability bounds needed when a caller caps an
assembled direct-game rejection estimate by one. The results are formalization-only
support: they do not bound any individual game branch or prove a passing-value theorem.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:178-186`
- Parent issue Dengnifer/MIPStarRE-QPBT-bak#119 and arithmetic issue
  Dengnifer/MIPStarRE-QPBT-bak#333
-/

@[expose] public section

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

namespace Strategy

/-- Every tensor-product strategy has nonnegative value. -/
theorem value_nonneg {G : _root_.MIPStarRE.QPBT.Game} (S : _root_.MIPStarRE.QPBT.Strategy G) : 0 ≤ S.value := by
  unfold _root_.MIPStarRE.QPBT.Strategy.value
  apply _root_.LIDT.MIPStarRE.LDT.avgOver_nonneg
  intro questions
  apply Finset.sum_nonneg
  intro answerA _
  apply Finset.sum_nonneg
  intro answerB _
  split
  · exact _root_.MIPStarRE.QPBT.outcomeWeight_nonneg S questions.1 questions.2 answerA answerB
  · exact le_rfl

end Strategy

/-- The total rejection probability of a directly indexed low-degree strategy is at
most one. This is the probability cap used by scalar error envelopes; it gives no
quantitative branch estimate. -/
theorem directLdRejectionProbability_le_one
    (D : _root_.MIPStarRE.QPBT.DirectLdParams) (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.directLdGame D)) :
    _root_.MIPStarRE.QPBT.directLdRejectionProbability D S ≤ 1 := by
  rw [_root_.MIPStarRE.QPBT.directLdRejectionProbability_eq_one_sub_value]
  linarith [S.value_nonneg]

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/ExtendedLineGame.lean. -/
/-!
# A direct-game strategy from supplied extended-line measurements

The input is an existing `ExtendedLinesWitness`, not an existence assertion
for that witness. Axis answers are restricted using its degree-support field;
diagonal answers are extended by zero coefficients. Point answers are the
scalar coarse-grainings of the supplied joint point measurements.

These are construction lemmas for the first paragraph of the proof of
`lem:qld-4-7`, not a proof of that lemma or of the existence of its input.
The remaining game-value estimates and the dependency on issue Dengnifer/MIPStarRE-QPBT-bak#119 are
recorded in `audits/2026-09-06_extended-line-game-244.md`.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1034`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1402`
- Blueprint `lem:qld-4-7` and `rem:qld-4-7-divisibility`.
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace ExtendedLineGame





























variable {params : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
variable {setting : _root_.MIPStarRE.QPBT.ProjectiveSetting params epsilon}
variable {points : _root_.MIPStarRE.QPBT.CombinedPointsWitness setting deltaQ}



























/-- Exact accounting of the seven potentially rejecting branches of the
constructed strategy. Same-type line branches are retained: their coefficient
equality checks do not follow merely from the answer tags. -/
theorem strategy_value_eq (lines : _root_.MIPStarRE.QPBT.ExtendedLinesWitness setting points deltaL) :
    (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines).value = 1 -
      (_root_.MIPStarRE.QPBT.directLdBranchRejectionProbability params.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
          (.point, .point) +
        _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability params.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
          (.point, .aline) +
        _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability params.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
          (.point, .dline) +
        _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability params.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
          (.aline, .point) +
        _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability params.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
          (.aline, .aline) +
        _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability params.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
          (.dline, .point) +
        _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability params.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
          (.dline, .dline)) / 9 := by
  have hvalue := _root_.MIPStarRE.QPBT.directLdRejectionProbability_eq_one_sub_value
    params.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
  rw [_root_.MIPStarRE.QPBT.directLdRejectionProbability, _root_.MIPStarRE.QPBT.avgOver_ldType_pair,
    _root_.MIPStarRE.QPBT.ExtendedLineGame.mixed_branch_rejection_eq_zero lines _ (Or.inl rfl),
    _root_.MIPStarRE.QPBT.ExtendedLineGame.mixed_branch_rejection_eq_zero lines _ (Or.inr rfl)] at hvalue
  linarith







end ExtendedLineGame

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/WitnessErrorNonneg.lean. -/
/-!
# Nonnegativity of combining-witness errors

This module derives nonnegativity of the error parameters supplied with the
combined point and extended line witnesses.  The point conclusion follows from
nonnegativity of state-dependent squared distance.  The line conclusion uses
the genuine bipartite POVMs underlying the completed line-point defect.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:689-709`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1034`
- Blueprint `lem:qld-4-10` and `lem:qld-4-13`.
- Issue Dengnifer/MIPStarRE-QPBT-bak#335.
-/

@[expose] public section

open scoped BigOperators MatrixOrder ComplexOrder

set_option synthInstance.maxSize 400

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

/-- This formalization-only auxiliary records that the error parameter of a supplied
`CombinedPointsWitness` is nonnegative. It supports `lem:qld-4-10`, paper lines
689--709, and does not construct or assert existence of the witness. -/
theorem CombinedPointsWitness.delta_nonneg {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaQ : ℝ}
    {setting : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon}
    (points : _root_.MIPStarRE.QPBT.CombinedPointsWitness setting deltaQ) :
    0 ≤ deltaQ := by
  exact le_trans
    (_root_.MIPStarRE.QPBT.DistanceCalculus.opFamilyDistSq_nonneg
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution
        ((Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) × (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)))
      (fun xz ab => setting.place .AA' ((points.Q .alice xz.1 xz.2).effect ab))
      (fun xz ab => setting.place .BA'' ((points.Q .bob xz.1 xz.2).effect ab))
      setting.psiHat)
    (points.self_consistent .AA' .BA'' trivial)



/-- This formalization-only auxiliary records that the error parameter of a supplied
`ExtendedLinesWitness` is nonnegative. It supports `lem:qld-4-13`, paper lines
1020--1034, and does not construct or assert existence of the witness. -/
theorem ExtendedLinesWitness.delta_nonneg {P : _root_.MIPStarRE.QPBT.AdmissibleParams}
    {epsilon deltaQ deltaL : ℝ} {setting : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon}
    {points : _root_.MIPStarRE.QPBT.CombinedPointsWitness setting deltaQ}
    (lines : _root_.MIPStarRE.QPBT.ExtendedLinesWitness setting points deltaL) :
    0 ≤ deltaL := by
  exact le_trans
    (_root_.MIPStarRE.QPBT.ExtendedLineGame.completedLinePointDefect_aaBa_nonneg lines
      (_root_.MIPStarRE.QPBT.directLinePointDist P.extendedDirectLd))
    lines.consistent_alice

end

end MIPStarRE.QPBT

/-!
# Passing value of the supplied extended-line strategy

This module assembles the seven potentially rejecting branches of the directly
indexed low-degree strategy constructed from an `ExtendedLinesWitness`.  It
then transports the resulting lower bound through the explicit Naimark
dilation.  These are formalization-only supplied-witness consequences; they do
not construct the witness or establish source theorem `lem:qld-4-7`.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1034`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`
- Blueprint `lem:qld-4-7`
- Issue Dengnifer/MIPStarRE-QPBT-bak#348
-/



open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement



open MIPStarRE.QPBT.ExtendedLineGame

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaQ deltaL : Real}
variable {setting : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon}
variable {points : _root_.MIPStarRE.QPBT.CombinedPointsWitness setting deltaQ}

theorem solution
    (lines : _root_.MIPStarRE.QPBT.ExtendedLinesWitness setting points deltaL) :
    1 - _root_.MIPStarRE.QPBT.directPassingErrorEnvelope (deltaQ + deltaL)
        ((P.m * P.d : Real) / (P.q : Real)) ≤
      (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines).value := by
  let rejection :=
    _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability P.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
          (.point, .point) +
        _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability P.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
          (.point, .aline) +
        _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability P.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
          (.point, .dline) +
        _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability P.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
          (.aline, .point) +
        _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability P.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
          (.aline, .aline) +
        _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability P.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
          (.dline, .point) +
        _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability P.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
          (.dline, .dline)
  have hsum : rejection ≤
      deltaQ + 16 * deltaL + 4 * Real.sqrt (deltaQ + 2 * deltaL) +
        5 * ((P.m * P.d : Real) / (P.q : Real)) := by
    exact _root_.MIPStarRE.QPBT.ExtendedLineGame.seven_branch_rejections_le lines
  have hcap : rejection / 9 ≤ 1 := by
    have h := _root_.MIPStarRE.QPBT.directLdRejectionProbability_le_one P.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
    rw [_root_.MIPStarRE.QPBT.directLdRejectionProbability_eq_one_sub_value, _root_.MIPStarRE.QPBT.ExtendedLineGame.strategy_value_eq lines] at h
    change rejection / 9 ≤ 1
    linarith
  have hraw : rejection / 9 ≤
      (deltaQ + 16 * deltaL + 4 * Real.sqrt (deltaQ + 2 * deltaL) +
        5 * ((P.m * P.d : Real) / (P.q : Real))) / 9 := by
    linarith
  have henvelope := _root_.MIPStarRE.QPBT.seven_branch_capped_error_le_directPassingErrorEnvelope
    deltaQ deltaL ((P.m * P.d : Real) / (P.q : Real))
    points.delta_nonneg lines.delta_nonneg (by positivity)
  have hrejection : rejection / 9 ≤
      _root_.MIPStarRE.QPBT.directPassingErrorEnvelope (deltaQ + deltaL)
        ((P.m * P.d : Real) / (P.q : Real)) :=
    (le_min hcap hraw).trans henvelope
  rw [_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy_value_eq lines]
  change 1 - _ ≤ 1 - rejection / 9
  linarith
