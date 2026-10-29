-- Prove2me | solution 1 for MIPStarRE.QPBT.lineRepMap_projX_directPointToPauli_lineRepMap
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:51:54.012985+00:00
-- url     : https://prove2.me/submissions/7f48ba87-cbf0-4eb6-831d-9f09403f3863

-- Generated proof for MIPStarRE.QPBT.lineRepMap_projX_directPointToPauli_lineRepMap.
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
import Definitions.Def_QPBT_QPBT_Combining_Defs
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Questions
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/Lines/SubLineBranch.lean. -/
/-!
# The branch data of the sub-line sampling procedure

The sampling procedure of the sub-line lemma draws a line kind, a stored
extended coordinate, and an unrestricted extended direction, and forms from
them the direction of the extended line: the elementary direction at the
stored coordinate in the axis branch, and the extended direction with the
coordinates preceding the stored coordinate replaced by zero in the diagonal
branch.  The two source lines are then read off the two coordinate blocks.
This module fixes the coordinate index that each source line must carry: the
stored coordinate itself when it belongs to that block, the first coordinate
otherwise.  With that choice the source block of the extended direction always
lies in the line spanned by the corresponding source direction, which is the
incidence hypothesis of the two projection lemmas.  The module also records
that moving an extended point to its canonical representative does not change
the canonical representative of either of its source blocks.

## References

The statements support `lem:qld-sublines` in
blueprint `lem:qld-sublines`, whose source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`.
The coordinate blocks are those of `def:combine-map`, blueprint lines
445--480, paper lines 970--989; the prefix truncation is that of
blueprint `def:ld-question-distribution`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

noncomputable section

/-! ## The three ranges of extended coordinates -/



/-! ## Linearity of the identification of the two scalar fields -/

/-- The identification of the two scalar fields is additive on extended
points.  Blueprint `def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem directPointToPauli_add (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (u v : Fin P.extendedDirectLd.m → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd) :
    _root_.MIPStarRE.QPBT.directPointToPauli P (u + v) =
      _root_.MIPStarRE.QPBT.directPointToPauli P u + _root_.MIPStarRE.QPBT.directPointToPauli P v := by
  funext i
  change _root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P (u i + v i) =
    _root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P (u i) + _root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P (v i)
  rw [map_add]

/-- The identification of the two scalar fields carries a scalar multiple of
an extended point to the multiple by the identified scalar.  Blueprint
`def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem directPointToPauli_smul (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (t : _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd)
    (u : Fin P.extendedDirectLd.m → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd) :
    _root_.MIPStarRE.QPBT.directPointToPauli P (t • u) =
      _root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P t • _root_.MIPStarRE.QPBT.directPointToPauli P u := by
  funext i
  change _root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P (t * u i) =
    _root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P t * _root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P (u i)
  rw [map_mul]

/-! ## The coordinate index carried by each source line -/























/-! ## The two directions of a branch -/





/-! ## Incidence of the two source blocks of a branch direction -/





/-! ## Canonical representatives of the two source blocks -/





end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/Lines/SubLineExtended.lean. -/
/-!
# Coordinate blocks of an extended point and of an extended direct sample

This module records the block decomposition used by the sampling procedure of
the sub-line lemma on the extended dimension.  A point of the extended space
is the tuple consisting of its two source point blocks and its two scalar
coordinates, and this decomposition is a bijection carrying the uniform law to
the uniform law; in particular the two source blocks of a uniform extended
point are independent and uniform.  The decomposition is linear, so it
commutes with the affine parameterization of a line, and it commutes with the
canonical identification of the extended scalar field with the source scalar
field.  The stored coordinate index of an extended direct sample splits along
the same three coordinate ranges.

## References

The decompositions support `lem:qld-sublines` in
blueprint `lem:qld-sublines`, whose source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`.
The coordinate blocks are those of `def:combine-map`, blueprint lines
445--480, paper lines 970--989.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

noncomputable section

/-! ## Linearity of the coordinate blocks -/

/-- The `X` block of a sum of extended points is the sum of the blocks.
Blueprint `def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem projX_add {K : Type*} [AddCommMonoid K] {m : ℕ}
    (u v : Fin (2 * m + 2) → K) :
    _root_.MIPStarRE.QPBT.projX (u + v) = _root_.MIPStarRE.QPBT.projX u + _root_.MIPStarRE.QPBT.projX v := rfl



/-- The `X` block of a scalar multiple of an extended point is the scalar
multiple of the block.  Blueprint `def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem projX_smul {K : Type*} [Monoid K] {m : ℕ} (t : K)
    (u : Fin (2 * m + 2) → K) :
    _root_.MIPStarRE.QPBT.projX (t • u) = t • _root_.MIPStarRE.QPBT.projX u := rfl



/-! ## The coordinate blocks of an extended point -/















/-! ## Transport to the source scalar field -/





/-! ## The blocks of an extended direct sample -/



/-! ## Compatibility data read off the coordinate blocks -/





end

end MIPStarRE.QPBT

/-!
# The branch data of the sub-line sampling procedure

The sampling procedure of the sub-line lemma draws a line kind, a stored
extended coordinate, and an unrestricted extended direction, and forms from
them the direction of the extended line: the elementary direction at the
stored coordinate in the axis branch, and the extended direction with the
coordinates preceding the stored coordinate replaced by zero in the diagonal
branch.  The two source lines are then read off the two coordinate blocks.
This module fixes the coordinate index that each source line must carry: the
stored coordinate itself when it belongs to that block, the first coordinate
otherwise.  With that choice the source block of the extended direction always
lies in the line spanned by the corresponding source direction, which is the
incidence hypothesis of the two projection lemmas.  The module also records
that moving an extended point to its canonical representative does not change
the canonical representative of either of its source blocks.

## References

The statements support `lem:qld-sublines` in
blueprint `lem:qld-sublines`, whose source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`.
The coordinate blocks are those of `def:combine-map`, blueprint lines
445--480, paper lines 970--989; the prefix truncation is that of
blueprint `def:ld-question-distribution`.
-/



open scoped BigOperators

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT



/-! ## The three ranges of extended coordinates -/



/-! ## Linearity of the identification of the two scalar fields -/





/-! ## The coordinate index carried by each source line -/























/-! ## The two directions of a branch -/





/-! ## Incidence of the two source blocks of a branch direction -/





/-! ## Canonical representatives of the two source blocks -/

theorem solution (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (v x : Fin P.extendedDirectLd.m → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd)
    (dX : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)
    (hdir : _root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P v) ∈
      Submodule.span (_root_.MIPStarRE.QPBT.PauliScalar P) ({dX} : Set (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))) :
    _root_.MIPStarRE.QPBT.lineRepMap dX (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P (_root_.MIPStarRE.QPBT.lineRepMap v x))) =
      _root_.MIPStarRE.QPBT.lineRepMap dX (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P x)) := by
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp (_root_.MIPStarRE.QPBT.sub_lineRepMap_mem_span v x)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hdir
  have hx : x = _root_.MIPStarRE.QPBT.lineRepMap v x + t • v := by
    rw [ht]
    abel
  have hstep : _root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P x) =
      _root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P (_root_.MIPStarRE.QPBT.lineRepMap v x)) +
        (_root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P t * c) • dX := by
    conv_lhs => rw [hx]
    rw [_root_.MIPStarRE.QPBT.directPointToPauli_add, _root_.MIPStarRE.QPBT.directPointToPauli_smul, _root_.MIPStarRE.QPBT.projX_add, _root_.MIPStarRE.QPBT.projX_smul,
      ← hc]
    module
  rw [hstep, _root_.MIPStarRE.QPBT.lineRepMap_add_smul]
