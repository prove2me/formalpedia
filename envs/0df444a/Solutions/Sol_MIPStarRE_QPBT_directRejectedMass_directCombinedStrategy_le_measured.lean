-- Prove2me | solution 1 for MIPStarRE.QPBT.directRejectedMass_directCombinedStrategy_le_measured
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:15:22.019275+00:00
-- url     : https://prove2.me/submissions/cd56b545-8a87-4dbd-bc22-3b22c600ee5a

-- Generated proof for MIPStarRE.QPBT.directRejectedMass_directCombinedStrategy_le_measured.
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
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_BranchComparison
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Answers
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Parameters
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Polynomial
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_QuestionLaw
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Strategy
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Value
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_WinPredicate
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_directCombinedWinTransport_aline_point
import Theorems.Thm_MIPStarRE_QPBT_directCombinedWinTransport_dline_point
import Theorems.Thm_MIPStarRE_QPBT_directCombinedWinTransport_point_aline
import Theorems.Thm_MIPStarRE_QPBT_directCombinedWinTransport_point_dline
import Theorems.Thm_MIPStarRE_QPBT_directCombined_measuredQuestion_of_coefficientVar
import Theorems.Thm_MIPStarRE_QPBT_directCombined_measuredQuestion_of_pointVar
import Theorems.Thm_MIPStarRE_QPBT_directRejectedMass_directCombinedStrategy_le

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/DirectLowDegree/Transport/Combining/WinPredicate.lean. -/
/-!
# Branch-wise acceptance transport for the combined strategy

By `directRejectedMass_directCombinedStrategy_le`, the branch-wise estimates of
`lem:ld-combined-value` reduce to the following statement: the relabelling of
`def:ld-combined-strategy` sends an answer pair accepted by the win predicate
of the original game at the measured questions to an answer pair accepted by
the win predicate of the combined game.  This module proves that statement for
each of the nine ordered type pairs of the combined game.

Three of the nine branches are deterministic.  The two questions of a branch
whose type pair is diagonal are equal, so the acceptance clause of the original
game forces the two measured outcomes to be equal, and the relabelling, being a
function, sends them to equal combined outcomes.  The two branches pairing an
axis-parallel line with a diagonal line impose no condition in either game.

The six remaining branches pair a line with a point, and split according to
whether the stored coordinate index of the common sample is a point coordinate
or a combining coordinate.  On a point coordinate the acceptance clause of the
combined game is obtained from the acceptance clause of the original game by
the affine change of parameter `directCombinedRebaseParameter`: the parameter
presenting the sampled point on the sampled line of the combined space presents
the point part of the sampled point on the image line, after the shift.  On a
combining coordinate the sampled line lies in a fiber of the projection to the
point coordinates, the combining part of the sampled point is the affine
function `α₀ + t w` of the parameter, and the acceptance clause of the combined
game is the identity `∑ r (α₀ + t w)_r b_r = ∑ r α_r b_r`.

All declarations below are formalization-only support for
`lem:ld-combined-value`; none is a paper-labelled result.

## References

* `references/neexp-paper/05_quantum_preliminaries.tex:1409-1503`
* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:526-568`
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries

noncomputable section

/-! ## The two parts of a point along a line -/







/-! ## Degree bounds at the combined parameters -/





/-! ## Evaluation of the combined answers -/







/-! ## Structural clauses of the win predicate -/

/-- An answer pair accepted at two equal questions of the directly indexed game
consists of two equal answers: the three diagonal clauses of
`def:ld-win-predicate` are equalities of answers. -/
theorem directLdAnswer_eq_of_win_self (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (q : _root_.MIPStarRE.QPBT.DirectLdQuestion D) {a b : _root_.MIPStarRE.QPBT.DirectLdAnswer D}
    (hwin : _root_.MIPStarRE.QPBT.directLdWinPredicate D q q a b = true) : a = b := by
  obtain ⟨t, xq⟩ := q
  cases t <;> cases a <;> cases b <;>
    simp_all [_root_.MIPStarRE.QPBT.directLdWinPredicate, _root_.MIPStarRE.QPBT.validDirectLdAnswer]

/-- Two equal answers of the correct constructor are accepted at two equal
questions of the directly indexed game. -/
theorem directLdWinPredicate_self (D : _root_.MIPStarRE.QPBT.DirectLdParams) (q : _root_.MIPStarRE.QPBT.DirectLdQuestion D)
    (a : _root_.MIPStarRE.QPBT.DirectLdAnswer D) (hvalid : _root_.MIPStarRE.QPBT.validDirectLdAnswer q.1 a = true) :
    _root_.MIPStarRE.QPBT.directLdWinPredicate D q q a a = true := by
  obtain ⟨t, xq⟩ := q
  cases t <;> cases a <;>
    simp_all [_root_.MIPStarRE.QPBT.directLdWinPredicate, _root_.MIPStarRE.QPBT.validDirectLdAnswer]

/-- The relabelling of `def:ld-combined-strategy` always produces an answer of
the constructor required by the type of the combined question. -/
theorem validDirectLdAnswer_directCombinedAnswerMap (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (q : _root_.MIPStarRE.QPBT.DirectLdQuestion D.combined) (a : _root_.MIPStarRE.QPBT.DirectLdAnswer D) :
    _root_.MIPStarRE.QPBT.validDirectLdAnswer q.1 (_root_.MIPStarRE.QPBT.directCombinedAnswerMap D q a) = true := by
  obtain ⟨t, xq⟩ := q
  cases t
  · rfl
  · rcases hsplit : _root_.MIPStarRE.QPBT.directCombinedIndexSplit D xq.index with j | r <;>
      simp only [_root_.MIPStarRE.QPBT.directCombinedAnswerMap, hsplit, _root_.MIPStarRE.QPBT.validDirectLdAnswer]
  · rcases hsplit : _root_.MIPStarRE.QPBT.directCombinedIndexSplit D xq.index with j | r <;>
      simp only [_root_.MIPStarRE.QPBT.directCombinedAnswerMap, hsplit, _root_.MIPStarRE.QPBT.validDirectLdAnswer]

/-- An ordered pair of a well-formed axis-parallel line answer and a well-formed
diagonal line answer is accepted: `def:ld-win-predicate` imposes no condition on
that ordered type pair. -/
theorem directLdWinPredicate_aline_dline (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (xq yq : _root_.MIPStarRE.QPBT.DirectLdSpace D) (a b : _root_.MIPStarRE.QPBT.DirectLdAnswer D)
    (ha : _root_.MIPStarRE.QPBT.validDirectLdAnswer _root_.MIPStarRE.QPBT.LdType.aline a = true)
    (hb : _root_.MIPStarRE.QPBT.validDirectLdAnswer _root_.MIPStarRE.QPBT.LdType.dline b = true) :
    _root_.MIPStarRE.QPBT.directLdWinPredicate D (.aline, xq) (.dline, yq) a b = true := by
  cases a <;> cases b <;> simp_all [_root_.MIPStarRE.QPBT.directLdWinPredicate, _root_.MIPStarRE.QPBT.validDirectLdAnswer]

/-- The mirror of `directLdWinPredicate_aline_dline`. -/
theorem directLdWinPredicate_dline_aline (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (xq yq : _root_.MIPStarRE.QPBT.DirectLdSpace D) (a b : _root_.MIPStarRE.QPBT.DirectLdAnswer D)
    (ha : _root_.MIPStarRE.QPBT.validDirectLdAnswer _root_.MIPStarRE.QPBT.LdType.dline a = true)
    (hb : _root_.MIPStarRE.QPBT.validDirectLdAnswer _root_.MIPStarRE.QPBT.LdType.aline b = true) :
    _root_.MIPStarRE.QPBT.directLdWinPredicate D (.dline, xq) (.aline, yq) a b = true := by
  cases a <;> cases b <;> simp_all [_root_.MIPStarRE.QPBT.directLdWinPredicate, _root_.MIPStarRE.QPBT.validDirectLdAnswer]

/-- A coordinate index of the combined dimension split off as a point
coordinate is that point coordinate. -/
theorem eq_combinedPointVar_of_indexSplit (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    {i : Fin D.combined.m} {j : Fin D.m}
    (h : _root_.MIPStarRE.QPBT.directCombinedIndexSplit D i = Sum.inl j) :
    i = _root_.MIPStarRE.QPBT.combinedPointVar D.m D.k j := by
  have hi : finSumFinEquiv (_root_.MIPStarRE.QPBT.directCombinedIndexSplit D i) =
      finSumFinEquiv (Sum.inl j) := congrArg _ h
  rw [_root_.MIPStarRE.QPBT.directCombinedIndexSplit, Equiv.apply_symm_apply] at hi
  exact hi

/-- A coordinate index of the combined dimension split off as a combining
coordinate is that combining coordinate. -/
theorem eq_combinedCoefficientVar_of_indexSplit (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    {i : Fin D.combined.m} {r : Fin D.k}
    (h : _root_.MIPStarRE.QPBT.directCombinedIndexSplit D i = Sum.inr r) :
    i = _root_.MIPStarRE.QPBT.combinedCoefficientVar D.m D.k r := by
  have hi : finSumFinEquiv (_root_.MIPStarRE.QPBT.directCombinedIndexSplit D i) =
      finSumFinEquiv (Sum.inr r) := congrArg _ h
  rw [_root_.MIPStarRE.QPBT.directCombinedIndexSplit, Equiv.apply_symm_apply] at hi
  exact hi

/-! ## The acceptance clause on a point coordinate -/





/-! ## The branch-wise acceptance transport -/











/-- A branch whose ordered type pair is diagonal: the two questions of the
combined game are equal, so the acceptance clause of the original game at the
two equal measured questions forces the two measured outcomes to be equal, and
the relabelling sends them to equal combined outcomes. -/
theorem directCombinedWinTransport_diagonal (D : _root_.MIPStarRE.QPBT.DirectLdParams) (t : _root_.MIPStarRE.QPBT.LdType)
    (sample : _root_.MIPStarRE.QPBT.DirectLdSpace D.combined) :
    _root_.MIPStarRE.QPBT.DirectCombinedWinTransport D t t sample := by
  intro a b hwin
  have hab : a = b := _root_.MIPStarRE.QPBT.directLdAnswer_eq_of_win_self D _ hwin
  subst hab
  exact _root_.MIPStarRE.QPBT.directLdWinPredicate_self D.combined (t, _root_.MIPStarRE.QPBT.directLdMap D.combined t sample) _
    (_root_.MIPStarRE.QPBT.validDirectLdAnswer_directCombinedAnswerMap D
      (t, _root_.MIPStarRE.QPBT.directLdMap D.combined t sample) a)

/-- The axis-parallel-line versus diagonal-line branch: the win predicate of
the combined game imposes no condition on that ordered type pair. -/
theorem directCombinedWinTransport_aline_dline (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (sample : _root_.MIPStarRE.QPBT.DirectLdSpace D.combined) :
    _root_.MIPStarRE.QPBT.DirectCombinedWinTransport D .aline .dline sample := by
  intro a b _
  exact _root_.MIPStarRE.QPBT.directLdWinPredicate_aline_dline D.combined _ _ _ _
    (_root_.MIPStarRE.QPBT.validDirectLdAnswer_directCombinedAnswerMap D
      (_root_.MIPStarRE.QPBT.LdType.aline, _root_.MIPStarRE.QPBT.directLdMap D.combined _root_.MIPStarRE.QPBT.LdType.aline sample) a)
    (_root_.MIPStarRE.QPBT.validDirectLdAnswer_directCombinedAnswerMap D
      (_root_.MIPStarRE.QPBT.LdType.dline, _root_.MIPStarRE.QPBT.directLdMap D.combined _root_.MIPStarRE.QPBT.LdType.dline sample) b)

/-- The diagonal-line versus axis-parallel-line branch. -/
theorem directCombinedWinTransport_dline_aline (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (sample : _root_.MIPStarRE.QPBT.DirectLdSpace D.combined) :
    _root_.MIPStarRE.QPBT.DirectCombinedWinTransport D .dline .aline sample := by
  intro a b _
  exact _root_.MIPStarRE.QPBT.directLdWinPredicate_dline_aline D.combined _ _ _ _
    (_root_.MIPStarRE.QPBT.validDirectLdAnswer_directCombinedAnswerMap D
      (_root_.MIPStarRE.QPBT.LdType.dline, _root_.MIPStarRE.QPBT.directLdMap D.combined _root_.MIPStarRE.QPBT.LdType.dline sample) a)
    (_root_.MIPStarRE.QPBT.validDirectLdAnswer_directCombinedAnswerMap D
      (_root_.MIPStarRE.QPBT.LdType.aline, _root_.MIPStarRE.QPBT.directLdMap D.combined _root_.MIPStarRE.QPBT.LdType.aline sample) b)

/-- The acceptance transport of `lem:ld-combined-value` on every one of the
nine ordered type pairs of the combined game.  This is the hypothesis of
`directRejectedMass_directCombinedStrategy_le` at the question pair attached to
a sample of the combined game. -/
theorem directCombinedWinTransport_all (D : _root_.MIPStarRE.QPBT.DirectLdParams) (t₁ t₂ : _root_.MIPStarRE.QPBT.LdType)
    (sample : _root_.MIPStarRE.QPBT.DirectLdSpace D.combined) :
    _root_.MIPStarRE.QPBT.DirectCombinedWinTransport D t₁ t₂ sample := by
  cases t₁ <;> cases t₂
  · exact _root_.MIPStarRE.QPBT.directCombinedWinTransport_diagonal D .point sample
  · exact _root_.MIPStarRE.QPBT.directCombinedWinTransport_point_aline D sample
  · exact _root_.MIPStarRE.QPBT.directCombinedWinTransport_point_dline D sample
  · exact _root_.MIPStarRE.QPBT.directCombinedWinTransport_aline_point D sample
  · exact _root_.MIPStarRE.QPBT.directCombinedWinTransport_diagonal D .aline sample
  · exact _root_.MIPStarRE.QPBT.directCombinedWinTransport_aline_dline D sample
  · exact _root_.MIPStarRE.QPBT.directCombinedWinTransport_dline_point D sample
  · exact _root_.MIPStarRE.QPBT.directCombinedWinTransport_dline_aline D sample
  · exact _root_.MIPStarRE.QPBT.directCombinedWinTransport_diagonal D .dline sample

end

end MIPStarRE.QPBT

/-!
# The value of the combined strategy

`lem:ld-combined-value` transports the value of a projective strategy along
`def:ld-combined-strategy`.  Both games weight their nine ordered type pairs
uniformly, so it suffices to bound the rejection probability of each branch of
the combined game by a bounded number of branch rejection probabilities of the
original game.  Splitting a branch according to the event of
`lem:ld-combined-question-law`, the branch conditioned on a point coordinate
index is the branch of the original game at the same ordered type pair, and the
branch conditioned on a combining coordinate index is the point-versus-point
branch of the original game; on each of the two events the relabelling of
`def:ld-combined-strategy` carries acceptance to acceptance, which is
`directCombinedWinTransport_all`.  Each branch of the combined game is therefore
rejected with probability at most the sum of two branch rejection probabilities
of the original game, and summing over the nine branches multiplies the
rejection probability by at most ten.

## References

* `references/neexp-paper/05_quantum_preliminaries.tex:1409-1503`
* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:526-568`
-/



open scoped BigOperators MatrixOrder Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries
open LIDT.MIPStarRE.Quantum

theorem solution (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.directLdGame D)) (types : _root_.MIPStarRE.QPBT.LdType × _root_.MIPStarRE.QPBT.LdType)
    (sample : _root_.MIPStarRE.QPBT.DirectLdSpace D.combined) :
    _root_.MIPStarRE.QPBT.directRejectedMass D.combined (_root_.MIPStarRE.QPBT.directCombinedStrategy D S)
        (types.1, _root_.MIPStarRE.QPBT.directLdMap D.combined types.1 sample)
        (types.2, _root_.MIPStarRE.QPBT.directLdMap D.combined types.2 sample) ≤
      _root_.MIPStarRE.QPBT.directCombinedMeasuredRejectedMass D S types sample.index
        (_root_.MIPStarRE.QPBT.directCombinedPointPart D sample.point,
          _root_.MIPStarRE.QPBT.directCombinedPointPart D sample.direction) := by
  refine le_trans (_root_.MIPStarRE.QPBT.directRejectedMass_directCombinedStrategy_le D S _ _
    (_root_.MIPStarRE.QPBT.directCombinedWinTransport_all D types.1 types.2 sample)) (le_of_eq ?_)
  rcases hsplit : _root_.MIPStarRE.QPBT.directCombinedIndexSplit D sample.index with j | r
  · have hindex : sample.index = _root_.MIPStarRE.QPBT.combinedPointVar D.m D.k j :=
      _root_.MIPStarRE.QPBT.eq_combinedPointVar_of_indexSplit D hsplit
    rw [_root_.MIPStarRE.QPBT.directCombined_measuredQuestion_of_pointVar D types.1 j sample hindex,
      _root_.MIPStarRE.QPBT.directCombined_measuredQuestion_of_pointVar D types.2 j sample hindex]
    simp only [_root_.MIPStarRE.QPBT.directCombinedMeasuredRejectedMass, hsplit,
      _root_.MIPStarRE.QPBT.directCombinedSampleProjection]
  · have hindex : sample.index = _root_.MIPStarRE.QPBT.combinedCoefficientVar D.m D.k r :=
      _root_.MIPStarRE.QPBT.eq_combinedCoefficientVar_of_indexSplit D hsplit
    rw [_root_.MIPStarRE.QPBT.directCombined_measuredQuestion_of_coefficientVar D types.1 r sample hindex,
      _root_.MIPStarRE.QPBT.directCombined_measuredQuestion_of_coefficientVar D types.2 r sample hindex]
    simp only [_root_.MIPStarRE.QPBT.directCombinedMeasuredRejectedMass, hsplit]
