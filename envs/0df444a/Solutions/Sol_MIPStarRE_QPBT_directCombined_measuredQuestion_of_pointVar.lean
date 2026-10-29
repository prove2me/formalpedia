-- Prove2me | solution 1 for MIPStarRE.QPBT.directCombined_measuredQuestion_of_pointVar
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:06:24.271235+00:00
-- url     : https://prove2.me/submissions/4a6a2756-8c79-4f41-81ba-a53e82cc8948

-- Generated proof for MIPStarRE.QPBT.directCombined_measuredQuestion_of_pointVar.
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
import Definitions.Def_QPBT_QPBT_Algebra_Lines
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Parameters
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Polynomial
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_QuestionLaw
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Strategy
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Questions
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Mathlib

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/DirectLowDegree/Geometry.lean. -/
/-!
# Geometry for the directly indexed low-degree game

This module defines the parameters, line carrier, and line-point distributions
for the directly indexed low-degree game.

## References

The line-point distributions originate in
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:243-272`.
The directly indexed repair is documented in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries
open LIDT.MIPStarRE.Quantum

noncomputable section

























/-- Zeroing the coordinates preceding a prefix index is idempotent: the
coordinates it leaves unchanged are exactly those it does not zero. -/
theorem directPrefixProjection_idem (D : _root_.MIPStarRE.QPBT.DirectLdParams) (i : Fin D.m)
    (v : Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) :
    _root_.MIPStarRE.QPBT.directPrefixProjection i (_root_.MIPStarRE.QPBT.directPrefixProjection i v) =
      _root_.MIPStarRE.QPBT.directPrefixProjection i v := by
  funext j
  unfold _root_.MIPStarRE.QPBT.directPrefixProjection
  split_ifs <;> rfl



/-! ## Finite direct-line carrier -/

















































end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/DirectLowDegree/Transport/Combining/QuestionLaw.lean. -/
attribute [local instance] _root_.MIPStarRE.QPBT.directCombinedIndexNonempty
/-!
# The questions measured by the combined strategy

`lem:ld-combined-question-law` identifies the pair of questions measured by the
combined strategy of `def:ld-combined-strategy` on a sample of the combined
game.  The coordinate index of the common sample is uniform on the `m + k`
coordinates of the combined dimension, and the identification splits according
to whether that index is a point coordinate or a combining coordinate.

On a point coordinate `j`, all three question types measure the canonical
question of the same type of the original game attached to the *projected*
sample `directCombinedSampleProjection`: the point part of the sampled point,
the index `j`, and the point part of the sampled direction.  This uses the
coordinate order of `def:ld-combining-map`: the point coordinates precede the
combining coordinates, so the coordinate direction of a point coordinate has
point part the corresponding coordinate direction, and the prefix projection at
a point coordinate restricts to the prefix projection at that coordinate of the
point part.

On a combining coordinate, every direction produced by the question
distribution has vanishing point part, so all three question types measure the
point question at the point part of the sampled point.

The projected sample is read from the *canonical* base of the combined line,
which need not project to the canonical base of the image line; the two agree
after rebasing along the image direction, which is
`lineRepMap_directCombinedPointPart_lineRepMap`.

## References

* `references/neexp-paper/05_quantum_preliminaries.tex:1409-1503`
* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:473-508`
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries

noncomputable section



/-! ## Coordinates of the combined dimension -/













/-! ## Canonical bases -/

private theorem directCombinedPointPart_sub_smul (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (z V : Fin D.combined.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) (c : _root_.MIPStarRE.QPBT.DirectScalarQ D) :
    _root_.MIPStarRE.QPBT.directCombinedPointPart D (z - c • V) =
      _root_.MIPStarRE.QPBT.directCombinedPointPart D z - c • _root_.MIPStarRE.QPBT.directCombinedPointPart D V :=
  rfl



/-- The canonical base of a line of the combined space projects to a point of
the image line, so rebasing its projection along the image direction returns
the canonical base of the image line.  The canonical base of a line of the
combined space need not itself project to the canonical base of its image; this
is why the answer relabellings of `def:ld-combined-strategy` carry the affine
shift `directCombinedRebaseParameter`. -/
theorem lineRepMap_directCombinedPointPart_lineRepMap (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (V z : Fin D.combined.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) :
    _root_.MIPStarRE.QPBT.lineRepMap (_root_.MIPStarRE.QPBT.directCombinedPointPart D V)
        (_root_.MIPStarRE.QPBT.directCombinedPointPart D (_root_.MIPStarRE.QPBT.lineRepMap V z)) =
      _root_.MIPStarRE.QPBT.lineRepMap (_root_.MIPStarRE.QPBT.directCombinedPointPart D V) (_root_.MIPStarRE.QPBT.directCombinedPointPart D z) := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (_root_.MIPStarRE.QPBT.sub_lineRepMap_mem_span V z)
  have hz : _root_.MIPStarRE.QPBT.lineRepMap V z = z - c • V := by rw [hc]; abel
  rw [hz, directCombinedPointPart_sub_smul, sub_eq_add_neg, ← neg_smul]
  exact _root_.MIPStarRE.QPBT.lineRepMap_add_smul _ _ (-c)

/-! ## The measured questions -/







/-! ## The law of the projected sample -/













end

end MIPStarRE.QPBT

/-!
# The questions measured by the combined strategy

`lem:ld-combined-question-law` identifies the pair of questions measured by the
combined strategy of `def:ld-combined-strategy` on a sample of the combined
game.  The coordinate index of the common sample is uniform on the `m + k`
coordinates of the combined dimension, and the identification splits according
to whether that index is a point coordinate or a combining coordinate.

On a point coordinate `j`, all three question types measure the canonical
question of the same type of the original game attached to the *projected*
sample `directCombinedSampleProjection`: the point part of the sampled point,
the index `j`, and the point part of the sampled direction.  This uses the
coordinate order of `def:ld-combining-map`: the point coordinates precede the
combining coordinates, so the coordinate direction of a point coordinate has
point part the corresponding coordinate direction, and the prefix projection at
a point coordinate restricts to the prefix projection at that coordinate of the
point part.

On a combining coordinate, every direction produced by the question
distribution has vanishing point part, so all three question types measure the
point question at the point part of the sampled point.

The projected sample is read from the *canonical* base of the combined line,
which need not project to the canonical base of the image line; the two agree
after rebasing along the image direction, which is
`lineRepMap_directCombinedPointPart_lineRepMap`.

## References

* `references/neexp-paper/05_quantum_preliminaries.tex:1409-1503`
* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:473-508`
-/



open scoped BigOperators

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries





/-! ## Coordinates of the combined dimension -/













/-! ## Canonical bases -/







/-! ## The measured questions -/
attribute [local instance] _root_.MIPStarRE.QPBT.directCombinedIndexNonempty

theorem solution (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (t : _root_.MIPStarRE.QPBT.LdType) (j : Fin D.m) (sample : _root_.MIPStarRE.QPBT.DirectLdSpace D.combined)
    (hindex : sample.index = _root_.MIPStarRE.QPBT.combinedPointVar D.m D.k j) :
    _root_.MIPStarRE.QPBT.directCombinedMeasuredQuestion D (t, _root_.MIPStarRE.QPBT.directLdMap D.combined t sample) =
      (t, _root_.MIPStarRE.QPBT.directLdMap D t (_root_.MIPStarRE.QPBT.directCombinedSampleProjection D j sample)) := by
  cases t with
  | point => rfl
  | aline =>
      have hbase := _root_.MIPStarRE.QPBT.lineRepMap_directCombinedPointPart_lineRepMap D
        (_root_.MIPStarRE.QPBT.coordinateDirection (_root_.MIPStarRE.QPBT.combinedPointVar D.m D.k j)) sample.point
      rw [_root_.MIPStarRE.QPBT.directCombinedPointPart_coordinateDirection_pointVar] at hbase
      simp only [_root_.MIPStarRE.QPBT.directLdMap, _root_.MIPStarRE.QPBT.directCombinedMeasuredQuestion, hindex,
        _root_.MIPStarRE.QPBT.directCombinedIndexSplit_combinedPointVar,
        _root_.MIPStarRE.QPBT.directCombinedSampleProjection]
      exact congrArg (fun x : Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D =>
        ((_root_.MIPStarRE.QPBT.LdType.aline, ⟨x, j, 0⟩) : _root_.MIPStarRE.QPBT.DirectLdQuestion D)) hbase
  | dline =>
      have hbase := _root_.MIPStarRE.QPBT.lineRepMap_directCombinedPointPart_lineRepMap D
        (_root_.MIPStarRE.QPBT.directPrefixProjection (_root_.MIPStarRE.QPBT.combinedPointVar D.m D.k j) sample.direction)
        sample.point
      rw [_root_.MIPStarRE.QPBT.directCombinedPointPart_directPrefixProjection_pointVar] at hbase
      simp only [_root_.MIPStarRE.QPBT.directLdMap, _root_.MIPStarRE.QPBT.directCombinedMeasuredQuestion, hindex,
        _root_.MIPStarRE.QPBT.directCombinedIndexSplit_combinedPointVar,
        _root_.MIPStarRE.QPBT.directCombinedSampleProjection,
        _root_.MIPStarRE.QPBT.directCombinedPointPart_directPrefixProjection_pointVar,
        _root_.MIPStarRE.QPBT.directPrefixProjection_idem]
      exact congrArg (fun x : Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D =>
        ((_root_.MIPStarRE.QPBT.LdType.dline, ⟨x, j,
          _root_.MIPStarRE.QPBT.directPrefixProjection j
            (_root_.MIPStarRE.QPBT.directCombinedPointPart D sample.direction)⟩) :
          _root_.MIPStarRE.QPBT.DirectLdQuestion D)) hbase
