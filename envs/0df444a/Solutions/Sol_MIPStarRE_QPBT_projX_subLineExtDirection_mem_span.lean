-- Prove2me | solution 1 for MIPStarRE.QPBT.projX_subLineExtDirection_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:59:22.637203+00:00
-- url     : https://prove2.me/submissions/f9f08d7c-cf32-4d64-af11-04800fb37b24

-- Generated proof for MIPStarRE.QPBT.projX_subLineExtDirection_mem_span.
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
import Definitions.Def_QPBT_QPBT_Combining_Lines_SubLineBranch
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_directPointToPauli_coordinateDirection
import Theorems.Thm_MIPStarRE_QPBT_extendedCoordinate_cases

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/Lines/SubLineUniform.lean. -/
/-!
# Uniform points of a line and the blocks of a coordinate direction

This module records the two elementary geometric inputs of the sampling
procedure of the sub-line lemma. First, for independent uniform inputs `u` in
the ambient coordinate space and `t` in the scalar field, the point
`lineRepMap v u + t • v` is uniform. This map on ambient-point--parameter pairs
has fibers of size `q`: for nonzero `v`, `u` varies over a coset of the span of
`v`, while its canonical representative and `t` are fixed; for zero `v`, `u`
is fixed and `t` is free. In averaged form this is the resampling identity used
by the line-point samplers: a quantity of the canonical representative and of
the point may equivalently be averaged over the point and an independent
uniform affine parameter along the direction. Second, the two coordinate
blocks of an elementary coordinate direction of the extended space are the
corresponding elementary direction of the source space in the block that
carries the coordinate, and zero in the other block and at the two scalar
coordinates.

## References

The two statements support `lem:qld-sublines` in
blueprint `lem:qld-sublines`, whose source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`.
The canonical representative map is blueprint
`def:line-representative`; the coordinate blocks are those of
blueprint `def:combine-map`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

noncomputable section

/-! ## The canonical representative for the zero direction -/



/-! ## Uniform points of a line -/



/-! ## Resampling a uniform point along its canonical line -/



/-! ## Injectivity of the two block embeddings -/

/-- The `X`-block coordinate embedding of `def:combine-map` is injective.
Blueprint `def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem embX_injective (m : ℕ) : Function.Injective (_root_.MIPStarRE.QPBT.embX m) := by
  intro i j hij
  simpa using (_root_.MIPStarRE.QPBT.finCombineEquiv m).symm.injective hij



/-! ## The blocks of an elementary coordinate direction -/

/-- The `X` block of the elementary direction at an `X`-block coordinate is
the elementary direction of the source space at that coordinate.  Blueprint
`def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem projX_coordinateDirection_embX {K : Type*} [Field K] {m : ℕ}
    (i : Fin m) :
    _root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.coordinateDirection (_root_.MIPStarRE.QPBT.embX m i) : Fin (2 * m + 2) → K) =
      _root_.MIPStarRE.QPBT.coordinateDirection i := by
  funext j
  simp [_root_.MIPStarRE.QPBT.projX, _root_.MIPStarRE.QPBT.coordinateDirection, Pi.single_apply, (_root_.MIPStarRE.QPBT.embX_injective m).eq_iff]

/-- The `X` block of the elementary direction at a `Z`-block coordinate
vanishes.  Blueprint `def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem projX_coordinateDirection_embZ {K : Type*} [Field K] {m : ℕ}
    (i : Fin m) :
    _root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.coordinateDirection (_root_.MIPStarRE.QPBT.embZ m i) : Fin (2 * m + 2) → K) = 0 := by
  funext j
  have hne : _root_.MIPStarRE.QPBT.embX m j ≠ _root_.MIPStarRE.QPBT.embZ m i := by
    intro h
    simpa using (_root_.MIPStarRE.QPBT.finCombineEquiv m).symm.injective h
  simp [_root_.MIPStarRE.QPBT.projX, _root_.MIPStarRE.QPBT.coordinateDirection, hne]

/-- The `X` block of the elementary direction at the first scalar coordinate
vanishes.  Blueprint `def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem projX_coordinateDirection_alphaVar {K : Type*} [Field K] {m : ℕ} :
    _root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.coordinateDirection (_root_.MIPStarRE.QPBT.alphaVar m) : Fin (2 * m + 2) → K) = 0 := by
  funext j
  have hne : _root_.MIPStarRE.QPBT.embX m j ≠ _root_.MIPStarRE.QPBT.alphaVar m := by
    intro h
    simpa using (_root_.MIPStarRE.QPBT.finCombineEquiv m).symm.injective h
  simp [_root_.MIPStarRE.QPBT.projX, _root_.MIPStarRE.QPBT.coordinateDirection, hne]

/-- The `X` block of the elementary direction at the second scalar coordinate
vanishes.  Blueprint `def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem projX_coordinateDirection_betaVar {K : Type*} [Field K] {m : ℕ} :
    _root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.coordinateDirection (_root_.MIPStarRE.QPBT.betaVar m) : Fin (2 * m + 2) → K) = 0 := by
  funext j
  have hne : _root_.MIPStarRE.QPBT.embX m j ≠ _root_.MIPStarRE.QPBT.betaVar m := by
    intro h
    simpa using (_root_.MIPStarRE.QPBT.finCombineEquiv m).symm.injective h
  simp [_root_.MIPStarRE.QPBT.projX, _root_.MIPStarRE.QPBT.coordinateDirection, hne]









/-! ## The coordinates occupied by the two blocks -/

/-- The `i`-th `X`-block coordinate of the extended space is its `i`-th
coordinate.  Blueprint `def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem embX_val (m : ℕ) (i : Fin m) : (_root_.MIPStarRE.QPBT.embX m i).val = i.val := rfl

/-- The `i`-th `Z`-block coordinate of the extended space is its `(m + i)`-th
coordinate.  Blueprint `def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem embZ_val (m : ℕ) (i : Fin m) : (_root_.MIPStarRE.QPBT.embZ m i).val = m + i.val := rfl

/-- The extended coordinate carrying the first scalar is the coordinate
`2 m`.  Blueprint `def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem alphaVar_val (m : ℕ) : (_root_.MIPStarRE.QPBT.alphaVar m).val = 2 * m := by
  simp [_root_.MIPStarRE.QPBT.alphaVar, _root_.MIPStarRE.QPBT.finCombineEquiv]

/-- The extended coordinate carrying the second scalar is the coordinate
`2 m + 1`.  Blueprint `def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem betaVar_val (m : ℕ) : (_root_.MIPStarRE.QPBT.betaVar m).val = 2 * m + 1 := by
  simp [_root_.MIPStarRE.QPBT.betaVar, _root_.MIPStarRE.QPBT.finCombineEquiv]

/-! ## The blocks of a point of an extended line -/







/-! ## Incidence of the blocks of an extended line -/







end

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





/-! ## The coordinate index carried by each source line -/







/-- At an `X`-block coordinate the source `X` line carries that coordinate. -/
theorem subLineXIndex_embX (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (i : Fin P.m) :
    _root_.MIPStarRE.QPBT.subLineXIndex P (_root_.MIPStarRE.QPBT.embX P.m i) = i := by
  have h : (_root_.MIPStarRE.QPBT.embX P.m i).val < P.m := by
    rw [_root_.MIPStarRE.QPBT.embX_val]
    exact i.isLt
  rw [_root_.MIPStarRE.QPBT.subLineXIndex, dif_pos h]
  exact Fin.ext (_root_.MIPStarRE.QPBT.embX_val P.m i)















/-! ## The two directions of a branch -/





/-! ## Incidence of the two source blocks of a branch direction -/





/-! ## Canonical representatives of the two source blocks -/





end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/Lines/SubLinePrefix.lean. -/
/-!
# Coordinate blocks of a truncated extended direction

This module computes the two source blocks of the direction of an extended
diagonal line.  That direction is obtained from an unrestricted extended
vector by zeroing the coordinates that precede the stored coordinate index,
so each source block is again a prefix truncation: when the stored index is
the `i`-th coordinate of a block, that block inherits the truncation at `i`,
every preceding block vanishes, and every later block is retained untruncated.
The computation is recorded after transport to the source scalar field, since
the extended direction and the source line directions are presented over the
two identified scalar fields.

## References

The block computations support `lem:qld-sublines` in
blueprint `lem:qld-sublines`, whose source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`.
The truncation is the prefix restriction of paper `eq:cl-dlnf`,
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:230-237`,
and blueprint `def:ld-question-distribution`; the coordinate blocks are those of
blueprint `def:combine-map`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

noncomputable section

/-! ## Truncation at the first coordinate -/



/-! ## The `X` block of a truncated extended direction -/

/-- The `X` block of an extended direction truncated at an `X`-block
coordinate is the `X` block truncated at that coordinate of the source space.
Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem projX_directPrefixProjection_embX (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (i : Fin P.m)
    (v : Fin P.extendedDirectLd.m → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd) :
    _root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P
        (_root_.MIPStarRE.QPBT.directPrefixProjection (D := P.extendedDirectLd) (_root_.MIPStarRE.QPBT.embX P.m i) v)) =
      _root_.MIPStarRE.QPBT.prefixProjection (P := P.toLdParams) i (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P v)) := by
  funext a
  change _root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P
      (if (_root_.MIPStarRE.QPBT.embX P.m a).val < (_root_.MIPStarRE.QPBT.embX P.m i).val then 0 else v (_root_.MIPStarRE.QPBT.embX P.m a)) =
    if a.val < i.val then 0 else _root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P (v (_root_.MIPStarRE.QPBT.embX P.m a))
  rw [_root_.MIPStarRE.QPBT.embX_val, _root_.MIPStarRE.QPBT.embX_val]
  by_cases h : a.val < i.val
  · rw [if_pos h, if_pos h, map_zero]
  · rw [if_neg h, if_neg h]

/-- The `X` block of an extended direction truncated at a `Z`-block
coordinate vanishes.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem projX_directPrefixProjection_embZ (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (i : Fin P.m)
    (v : Fin P.extendedDirectLd.m → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd) :
    _root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P
      (_root_.MIPStarRE.QPBT.directPrefixProjection (D := P.extendedDirectLd) (_root_.MIPStarRE.QPBT.embZ P.m i) v)) = 0 := by
  funext a
  have ha : a.val < P.m := a.isLt
  change _root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P
      (if (_root_.MIPStarRE.QPBT.embX P.m a).val < (_root_.MIPStarRE.QPBT.embZ P.m i).val then 0 else v (_root_.MIPStarRE.QPBT.embX P.m a)) =
    (0 : _root_.MIPStarRE.QPBT.PauliScalar P)
  rw [_root_.MIPStarRE.QPBT.embX_val, _root_.MIPStarRE.QPBT.embZ_val, if_pos (by omega), map_zero]

/-- The `X` block of an extended direction truncated at the first scalar
coordinate vanishes.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem projX_directPrefixProjection_alphaVar (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (v : Fin P.extendedDirectLd.m → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd) :
    _root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P
      (_root_.MIPStarRE.QPBT.directPrefixProjection (D := P.extendedDirectLd) (_root_.MIPStarRE.QPBT.alphaVar P.m) v)) = 0 := by
  funext a
  have ha : a.val < P.m := a.isLt
  change _root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P
      (if (_root_.MIPStarRE.QPBT.embX P.m a).val < (_root_.MIPStarRE.QPBT.alphaVar P.m).val then 0 else v (_root_.MIPStarRE.QPBT.embX P.m a)) =
    (0 : _root_.MIPStarRE.QPBT.PauliScalar P)
  rw [_root_.MIPStarRE.QPBT.embX_val, _root_.MIPStarRE.QPBT.alphaVar_val, if_pos (by omega), map_zero]

/-- The `X` block of an extended direction truncated at the second scalar
coordinate vanishes.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem projX_directPrefixProjection_betaVar (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (v : Fin P.extendedDirectLd.m → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd) :
    _root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P
      (_root_.MIPStarRE.QPBT.directPrefixProjection (D := P.extendedDirectLd) (_root_.MIPStarRE.QPBT.betaVar P.m) v)) = 0 := by
  funext a
  have ha : a.val < P.m := a.isLt
  change _root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P
      (if (_root_.MIPStarRE.QPBT.embX P.m a).val < (_root_.MIPStarRE.QPBT.betaVar P.m).val then 0 else v (_root_.MIPStarRE.QPBT.embX P.m a)) =
    (0 : _root_.MIPStarRE.QPBT.PauliScalar P)
  rw [_root_.MIPStarRE.QPBT.embX_val, _root_.MIPStarRE.QPBT.betaVar_val, if_pos (by omega), map_zero]

/-! ## The `Z` block of a truncated extended direction -/









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

theorem solution (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (kind : _root_.MIPStarRE.QPBT.LineKind) (k : Fin (2 * P.m + 2))
    (w : Fin P.extendedDirectLd.m → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd) :
    _root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P (_root_.MIPStarRE.QPBT.subLineExtDirection P kind k w)) ∈
      Submodule.span (_root_.MIPStarRE.QPBT.PauliScalar P)
        (Set.singleton (_root_.MIPStarRE.QPBT.subLineSourceDirection P kind (_root_.MIPStarRE.QPBT.subLineXIndex P k)
          (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P w)))) := by
  rcases _root_.MIPStarRE.QPBT.extendedCoordinate_cases P.m k with ⟨i, rfl⟩ | ⟨j, rfl⟩ | rfl | rfl <;>
    cases kind
  · have hval : _root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P
        (_root_.MIPStarRE.QPBT.coordinateDirection (_root_.MIPStarRE.QPBT.embX P.m i))) =
        (_root_.MIPStarRE.QPBT.coordinateDirection i : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) := by
      exact (congrArg _root_.MIPStarRE.QPBT.projX
        (_root_.MIPStarRE.QPBT.directPointToPauli_coordinateDirection P (_root_.MIPStarRE.QPBT.embX P.m i))).trans
          (_root_.MIPStarRE.QPBT.projX_coordinateDirection_embX i)
    rw [_root_.MIPStarRE.QPBT.subLineXIndex_embX]
    change _root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P
      (_root_.MIPStarRE.QPBT.coordinateDirection (_root_.MIPStarRE.QPBT.embX P.m i))) ∈ _
    rw [hval]
    exact Submodule.mem_span_singleton_self _
  · rw [_root_.MIPStarRE.QPBT.subLineXIndex_embX]
    change _root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P
      (_root_.MIPStarRE.QPBT.directPrefixProjection (D := P.extendedDirectLd) (_root_.MIPStarRE.QPBT.embX P.m i) w)) ∈ _
    rw [_root_.MIPStarRE.QPBT.projX_directPrefixProjection_embX]
    exact Submodule.mem_span_singleton_self _
  · have hval : _root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P
        (_root_.MIPStarRE.QPBT.coordinateDirection (_root_.MIPStarRE.QPBT.embZ P.m j))) = 0 := by
      exact (congrArg _root_.MIPStarRE.QPBT.projX
        (_root_.MIPStarRE.QPBT.directPointToPauli_coordinateDirection P (_root_.MIPStarRE.QPBT.embZ P.m j))).trans
          (_root_.MIPStarRE.QPBT.projX_coordinateDirection_embZ j)
    change _root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P
      (_root_.MIPStarRE.QPBT.coordinateDirection (_root_.MIPStarRE.QPBT.embZ P.m j))) ∈ _
    rw [hval]
    exact Submodule.zero_mem _
  · change _root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P
      (_root_.MIPStarRE.QPBT.directPrefixProjection (D := P.extendedDirectLd) (_root_.MIPStarRE.QPBT.embZ P.m j) w)) ∈ _
    rw [_root_.MIPStarRE.QPBT.projX_directPrefixProjection_embZ]
    exact Submodule.zero_mem _
  · have hval : _root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P
        (_root_.MIPStarRE.QPBT.coordinateDirection (_root_.MIPStarRE.QPBT.alphaVar P.m))) = 0 := by
      exact (congrArg _root_.MIPStarRE.QPBT.projX
        (_root_.MIPStarRE.QPBT.directPointToPauli_coordinateDirection P (_root_.MIPStarRE.QPBT.alphaVar P.m))).trans
          _root_.MIPStarRE.QPBT.projX_coordinateDirection_alphaVar
    change _root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P
      (_root_.MIPStarRE.QPBT.coordinateDirection (_root_.MIPStarRE.QPBT.alphaVar P.m))) ∈ _
    rw [hval]
    exact Submodule.zero_mem _
  · change _root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P
      (_root_.MIPStarRE.QPBT.directPrefixProjection (D := P.extendedDirectLd) (_root_.MIPStarRE.QPBT.alphaVar P.m) w)) ∈ _
    rw [_root_.MIPStarRE.QPBT.projX_directPrefixProjection_alphaVar]
    exact Submodule.zero_mem _
  · have hval : _root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P
        (_root_.MIPStarRE.QPBT.coordinateDirection (_root_.MIPStarRE.QPBT.betaVar P.m))) = 0 := by
      exact (congrArg _root_.MIPStarRE.QPBT.projX
        (_root_.MIPStarRE.QPBT.directPointToPauli_coordinateDirection P (_root_.MIPStarRE.QPBT.betaVar P.m))).trans
          _root_.MIPStarRE.QPBT.projX_coordinateDirection_betaVar
    change _root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P
      (_root_.MIPStarRE.QPBT.coordinateDirection (_root_.MIPStarRE.QPBT.betaVar P.m))) ∈ _
    rw [hval]
    exact Submodule.zero_mem _
  · change _root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P
      (_root_.MIPStarRE.QPBT.directPrefixProjection (D := P.extendedDirectLd) (_root_.MIPStarRE.QPBT.betaVar P.m) w)) ∈ _
    rw [_root_.MIPStarRE.QPBT.projX_directPrefixProjection_betaVar]
    exact Submodule.zero_mem _
