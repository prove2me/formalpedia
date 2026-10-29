-- Prove2me | solution 1 for MIPStarRE.QPBT.directRejectedMass_directCombinedStrategy_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:11:08.308914+00:00
-- url     : https://prove2.me/submissions/8ba12bf8-8f01-470f-afd1-2c82ede79dd1

-- Generated proof for MIPStarRE.QPBT.directRejectedMass_directCombinedStrategy_le.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_BranchComparison
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Parameters
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Strategy
import Definitions.Def_QPBT_QPBT_Games_Defs
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_outcomeWeight_directCombinedStrategy

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
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
# Index-conditioned rejection probabilities of the directly indexed game

`lem:ld-combined-value` transports the value of a strategy along
`def:ld-combined-strategy` by splitting each branch of the combined game
according to the event of `lem:ld-combined-question-law`, that is according to
whether the stored coordinate index of the common sample is a point coordinate
or a combining coordinate.  This module provides the corresponding refinement
of the branch rejection probability: the uniform average over the common sample
is the uniform average over the stored coordinate index of the average over the
sampled point and the sampled direction alone.

The point-versus-point branch is recorded separately, because it is the branch
that the combining coordinates of the combined game reduce to: both of its
questions are the point question at the sampled point, so its rejected mass
depends on neither the stored coordinate index nor the sampled direction.

All declarations below are formalization-only support derived from the game
value; none is a paper-labelled result.

## References

* `references/neexp-paper/05_quantum_preliminaries.tex:1409-1503`
* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:517-568`
-/



open scoped BigOperators MatrixOrder Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries
open LIDT.MIPStarRE.Quantum



/-! ## The index-conditioned branch rejection probability -/







/-! ## The point-versus-point branch -/





/-! ## The rejected mass of the combined strategy -/

theorem solution (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.directLdGame D)) (x y : _root_.MIPStarRE.QPBT.DirectLdQuestion D.combined)
    (himp : ∀ a b : _root_.MIPStarRE.QPBT.DirectLdAnswer D,
      _root_.MIPStarRE.QPBT.directLdWinPredicate D (_root_.MIPStarRE.QPBT.directCombinedMeasuredQuestion D x)
          (_root_.MIPStarRE.QPBT.directCombinedMeasuredQuestion D y) a b = true →
        _root_.MIPStarRE.QPBT.directLdWinPredicate D.combined x y
          (_root_.MIPStarRE.QPBT.directCombinedAnswerMap D x a) (_root_.MIPStarRE.QPBT.directCombinedAnswerMap D y b) = true) :
    _root_.MIPStarRE.QPBT.directRejectedMass D.combined (_root_.MIPStarRE.QPBT.directCombinedStrategy D S) x y ≤
      _root_.MIPStarRE.QPBT.directRejectedMass D S (_root_.MIPStarRE.QPBT.directCombinedMeasuredQuestion D x)
        (_root_.MIPStarRE.QPBT.directCombinedMeasuredQuestion D y) := by
  classical
  set mx := _root_.MIPStarRE.QPBT.directCombinedMeasuredQuestion D x with hmx
  set my := _root_.MIPStarRE.QPBT.directCombinedMeasuredQuestion D y with hmy
  set F : _root_.MIPStarRE.QPBT.DirectLdAnswer D → _root_.MIPStarRE.QPBT.DirectLdAnswer D → ℝ := fun a b =>
    if _root_.MIPStarRE.QPBT.directLdWinPredicate D.combined x y
        (_root_.MIPStarRE.QPBT.directCombinedAnswerMap D x a) (_root_.MIPStarRE.QPBT.directCombinedAnswerMap D y b) then 0
    else _root_.MIPStarRE.QPBT.outcomeWeight S mx my a b with hF
  have hmass : _root_.MIPStarRE.QPBT.directRejectedMass D.combined (_root_.MIPStarRE.QPBT.directCombinedStrategy D S) x y =
      ∑ a : _root_.MIPStarRE.QPBT.DirectLdAnswer D, ∑ b : _root_.MIPStarRE.QPBT.DirectLdAnswer D, F a b := by
    have step : ∀ a' b' : _root_.MIPStarRE.QPBT.DirectLdAnswer D.combined,
        (if _root_.MIPStarRE.QPBT.directLdWinPredicate D.combined x y a' b' then 0
          else _root_.MIPStarRE.QPBT.outcomeWeight (_root_.MIPStarRE.QPBT.directCombinedStrategy D S) x y a' b') =
          ∑ a ∈ Finset.univ.filter (fun a => _root_.MIPStarRE.QPBT.directCombinedAnswerMap D x a = a'),
            ∑ b ∈ Finset.univ.filter (fun b => _root_.MIPStarRE.QPBT.directCombinedAnswerMap D y b = b'),
              F a b := by
      intro a' b'
      by_cases hw : _root_.MIPStarRE.QPBT.directLdWinPredicate D.combined x y a' b' = true
      · rw [if_pos hw]
        refine (Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun b hb => ?_).symm
        rw [Finset.mem_filter] at ha hb
        rw [hF]
        simp only [ha.2, hb.2, hw, if_true]
      · rw [if_neg hw, _root_.MIPStarRE.QPBT.outcomeWeight_directCombinedStrategy]
        refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
        rw [Finset.mem_filter] at ha hb
        simp [hF, ha.2, hb.2, hw, hmx, hmy]
    rw [_root_.MIPStarRE.QPBT.directRejectedMass]
    simp_rw [step]
    rw [← Finset.sum_fiberwise Finset.univ (_root_.MIPStarRE.QPBT.directCombinedAnswerMap D x)
      (fun a => ∑ b : _root_.MIPStarRE.QPBT.DirectLdAnswer D, F a b)]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ =>
      Finset.sum_fiberwise Finset.univ (_root_.MIPStarRE.QPBT.directCombinedAnswerMap D y) (F a)
  rw [hmass, _root_.MIPStarRE.QPBT.directRejectedMass]
  refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
  simp only [hF]
  by_cases hw : _root_.MIPStarRE.QPBT.directLdWinPredicate D mx my a b = true
  · simp only [if_pos hw, if_pos (himp a b hw), le_refl]
  · rw [if_neg hw]
    split_ifs
    · exact _root_.MIPStarRE.QPBT.outcomeWeight_nonneg S mx my a b
    · exact le_rfl
