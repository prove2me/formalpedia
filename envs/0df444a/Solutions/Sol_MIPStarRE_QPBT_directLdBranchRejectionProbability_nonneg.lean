-- Prove2me | solution 1 for MIPStarRE.QPBT.directLdBranchRejectionProbability_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T20:57:53.892756+00:00
-- url     : https://prove2.me/submissions/47f0bc7c-ba01-4460-8c64-15b8136b0ad4

-- Generated proof for MIPStarRE.QPBT.directLdBranchRejectionProbability_nonneg.
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
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_GameValue
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Mathlib

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
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



open scoped BigOperators MatrixOrder Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.Quantum

theorem solution
    (D : _root_.MIPStarRE.QPBT.DirectLdParams) (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.directLdGame D))
    (types : _root_.MIPStarRE.QPBT.LdType × _root_.MIPStarRE.QPBT.LdType) :
    0 ≤ _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability D S types := by
  apply _root_.LIDT.MIPStarRE.LDT.avgOver_nonneg
  intro sample
  apply Finset.sum_nonneg
  intro a _
  apply Finset.sum_nonneg
  intro b _
  by_cases h : _root_.MIPStarRE.QPBT.directLdWinPredicate D
      (types.1, _root_.MIPStarRE.QPBT.directLdMap D types.1 sample)
      (types.2, _root_.MIPStarRE.QPBT.directLdMap D types.2 sample) a b
  · simp [h]
  · simpa [h] using _root_.MIPStarRE.QPBT.outcomeWeight_nonneg S
      (types.1, _root_.MIPStarRE.QPBT.directLdMap D types.1 sample)
      (types.2, _root_.MIPStarRE.QPBT.directLdMap D types.2 sample) a b
