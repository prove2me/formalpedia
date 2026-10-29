-- Prove2me | solution 1 for MIPStarRE.QPBT.directPointToPauli_coordinateDirection
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:55:47.155222+00:00
-- url     : https://prove2.me/submissions/1e559dbf-b300-4702-917d-f16da68827bb

-- Generated proof for MIPStarRE.QPBT.directPointToPauli_coordinateDirection.
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
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

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



open scoped BigOperators

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT



/-! ## The canonical representative for the zero direction -/



/-! ## Uniform points of a line -/



/-! ## Resampling a uniform point along its canonical line -/



/-! ## Injectivity of the two block embeddings -/





/-! ## The blocks of an elementary coordinate direction -/

















/-! ## The coordinates occupied by the two blocks -/









/-! ## The blocks of a point of an extended line -/







/-! ## Incidence of the blocks of an extended line -/

theorem solution (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (k : Fin P.extendedDirectLd.m) :
    _root_.MIPStarRE.QPBT.directPointToPauli P (_root_.MIPStarRE.QPBT.coordinateDirection k) = _root_.MIPStarRE.QPBT.coordinateDirection k := by
  change Fin (2 * P.m + 2) at k
  funext j
  by_cases h : k = j
  · subst j
    change _root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P
        ((Pi.single k 1 : Fin (2 * P.m + 2) →
          _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd) k) =
      (Pi.single k 1 : Fin (2 * P.m + 2) → _root_.MIPStarRE.QPBT.PauliScalar P) k
    rw [Pi.single_eq_same, map_one]
  · change _root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P
        ((Pi.single k 1 : Fin (2 * P.m + 2) →
          _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd) j) =
      (Pi.single k 1 : Fin (2 * P.m + 2) → _root_.MIPStarRE.QPBT.PauliScalar P) j
    rw [Pi.single_eq_of_ne (Ne.symm h), map_zero]
