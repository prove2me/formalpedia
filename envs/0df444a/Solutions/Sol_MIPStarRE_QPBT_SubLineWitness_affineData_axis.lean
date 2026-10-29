-- Prove2me | solution 1 for MIPStarRE.QPBT.SubLineWitness.affineData_axis
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:59:22.675092+00:00
-- url     : https://prove2.me/submissions/c57b3647-545e-4683-a702-ca4323355aef

-- Generated proof for MIPStarRE.QPBT.SubLineWitness.affineData_axis.
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
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_Lines
import Definitions.Def_QPBT_QPBT_Combining_Defs
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLines_Measurement
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_directPointToPauli_coordinateDirection

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus

/- Source helpers from QPBT/Combining/ExtendedLines/Measurement.lean. -/
/-!
# Conditional extended-line measurements

This directly indexed auxiliary construction follows the first consistency
route for combined lines. The question carrier, completed answer alphabet,
and corrected error convention retain their existing meanings.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1118-1246`,
blueprint `lem:qld-4-13-established`.
See `docs/paper-gaps/qpbt_combined-lines-error-term.tex` and
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex` for the remaining
comparison with the printed source theorem.
-/

@[expose] public section

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open scoped BigOperators Matrix MatrixOrder ComplexOrder

noncomputable section

















/-- The selected coordinates satisfy the source's affine line identities. -/
theorem SubLineWitness.affineData_compatible {params : _root_.MIPStarRE.QPBT.AdmissibleParams}
    (sublines : _root_.MIPStarRE.QPBT.SubLineWitness params) (sample : _root_.MIPStarRE.QPBT.SubLineTriple params)
    (hsample : sample ∈ sublines.D.support) :
    let data := sublines.affineData sample hsample
    _root_.MIPStarRE.QPBT.IsCombineLineCompatible (_root_.MIPStarRE.QPBT.directPointToPauli params sample.1.base)
      (_root_.MIPStarRE.QPBT.directPointToPauli params sample.1.direction)
      sample.2.1.base sample.2.1.direction sample.2.2.base sample.2.2.direction
      (data 0) (data 1) (data 2) (data 3) (data 4) (data 5) (data 6) (data 7) :=
  Classical.choose_spec (sublines.exists_affineData sample hsample)





















/-- Axis directions in the source line carrier are nonzero. -/
private theorem source_axis_direction_ne_zero {params : _root_.MIPStarRE.QPBT.LdParams}
    (line : _root_.MIPStarRE.QPBT.LineDesc params) (haxis : line.kind = .axis) : line.direction ≠ 0 := by
  cases line with
  | axis base seed baseFixed =>
    intro hzero
    have hcoordinate := congrFun hzero (_root_.MIPStarRE.QPBT.chiIndex params seed)
    simp [_root_.MIPStarRE.QPBT.LineDesc.direction, _root_.MIPStarRE.QPBT.coordinateDirection] at hcoordinate
  | diagonal => cases haxis

/-- Two equal points on a nonzero affine direction force the parameter slope to vanish. -/
private theorem affine_slope_eq_zero {Scalar : Type*} [Field Scalar] {dimension : ℕ}
    {point base direction : Fin dimension → Scalar} {offset slope : Scalar}
    (hdirection : direction ≠ 0) (hzero : point = base + offset • direction)
    (hone : point = base + (offset + slope) • direction) : slope = 0 := by
  have hequal := add_left_cancel (hzero.symm.trans hone)
  have hvanish : slope • direction = 0 := by
    apply add_left_cancel (a := offset • direction)
    simpa only [add_smul, add_zero] using hequal.symm
  exact (smul_eq_zero.mp hvanish).resolve_right hdirection








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

/-- The `Z` block of a sum of extended points is the sum of the blocks.
Blueprint `def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem projZ_add {K : Type*} [AddCommMonoid K] {m : ℕ}
    (u v : Fin (2 * m + 2) → K) :
    _root_.MIPStarRE.QPBT.projZ (u + v) = _root_.MIPStarRE.QPBT.projZ u + _root_.MIPStarRE.QPBT.projZ v := rfl





/-! ## The coordinate blocks of an extended point -/















/-! ## Transport to the source scalar field -/





/-! ## The blocks of an extended direct sample -/



/-! ## Compatibility data read off the coordinate blocks -/





end

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





/-! ## The blocks of an elementary coordinate direction -/





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





/-- The `Z` block of the elementary direction at the first scalar coordinate
vanishes.  Blueprint `def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem projZ_coordinateDirection_alphaVar {K : Type*} [Field K] {m : ℕ} :
    _root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.coordinateDirection (_root_.MIPStarRE.QPBT.alphaVar m) : Fin (2 * m + 2) → K) = 0 := by
  funext j
  have hne : _root_.MIPStarRE.QPBT.embZ m j ≠ _root_.MIPStarRE.QPBT.alphaVar m := by
    intro h
    simpa using (_root_.MIPStarRE.QPBT.finCombineEquiv m).symm.injective h
  simp [_root_.MIPStarRE.QPBT.projZ, _root_.MIPStarRE.QPBT.coordinateDirection, hne]

/-- The `Z` block of the elementary direction at the second scalar coordinate
vanishes.  Blueprint `def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem projZ_coordinateDirection_betaVar {K : Type*} [Field K] {m : ℕ} :
    _root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.coordinateDirection (_root_.MIPStarRE.QPBT.betaVar m) : Fin (2 * m + 2) → K) = 0 := by
  funext j
  have hne : _root_.MIPStarRE.QPBT.embZ m j ≠ _root_.MIPStarRE.QPBT.betaVar m := by
    intro h
    simpa using (_root_.MIPStarRE.QPBT.finCombineEquiv m).symm.injective h
  simp [_root_.MIPStarRE.QPBT.projZ, _root_.MIPStarRE.QPBT.coordinateDirection, hne]

/-! ## The coordinates occupied by the two blocks -/









/-! ## The blocks of a point of an extended line -/







/-! ## Incidence of the blocks of an extended line -/







end

end MIPStarRE.QPBT

/-!
# Conditional extended-line measurements

This directly indexed auxiliary construction follows the first consistency
route for combined lines. The question carrier, completed answer alphabet,
and corrected error convention retain their existing meanings.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1118-1246`,
blueprint `lem:qld-4-13-established`.
See `docs/paper-gaps/qpbt_combined-lines-error-term.tex` and
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex` for the remaining
comparison with the printed source theorem.
-/



open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open scoped BigOperators Matrix MatrixOrder ComplexOrder

theorem solution {params : _root_.MIPStarRE.QPBT.AdmissibleParams}
    (sublines : _root_.MIPStarRE.QPBT.SubLineWitness params) (sample : _root_.MIPStarRE.QPBT.SubLineTriple params)
    (hsample : sample ∈ sublines.D.support) (haxis : sample.1.kind = .axis) :
    let data := sublines.affineData sample hsample
    (data 5 = 0 ∧ data 7 = 0) ∨ (data 1 = 0 ∧ data 3 = 0) := by
  let data := sublines.affineData sample hsample
  have hcompat := sublines.affineData_compatible sample hsample
  have hsource := sublines.axis_closure sample hsample haxis
  have hcoordinate : _root_.MIPStarRE.QPBT.directPointToPauli params sample.1.direction =
      _root_.MIPStarRE.QPBT.coordinateDirection sample.1.index := by
    rcases sample with ⟨line, pair⟩
    cases line with
    | axis => exact _root_.MIPStarRE.QPBT.directPointToPauli_coordinateDirection params _
    | diagonal => cases haxis
  by_cases hspecial : sample.1.index = _root_.MIPStarRE.QPBT.alphaVar params.m ∨ sample.1.index = _root_.MIPStarRE.QPBT.betaVar params.m
  · right
    have hprojection : _root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli params sample.1.direction) = 0 ∧
        _root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli params sample.1.direction) = 0 := by
      rw [hcoordinate]
      rcases hspecial with halpha | hbeta
      · rw [halpha]
        exact ⟨_root_.MIPStarRE.QPBT.projX_coordinateDirection_alphaVar, _root_.MIPStarRE.QPBT.projZ_coordinateDirection_alphaVar⟩
      · rw [hbeta]
        exact ⟨_root_.MIPStarRE.QPBT.projX_coordinateDirection_betaVar, _root_.MIPStarRE.QPBT.projZ_coordinateDirection_betaVar⟩
    have hzero := hcompat.2.2.2.2 (0 : _root_.MIPStarRE.QPBT.PauliScalar params)
    have hone := hcompat.2.2.2.2 (1 : _root_.MIPStarRE.QPBT.PauliScalar params)
    simp only [zero_smul, add_zero, mul_zero] at hzero
    simp only [one_smul, mul_one, _root_.MIPStarRE.QPBT.projX_add, _root_.MIPStarRE.QPBT.projZ_add, hprojection.1, hprojection.2,
      add_zero] at hone
    exact ⟨affine_slope_eq_zero (Scalar := _root_.MIPStarRE.QPBT.PauliScalar params)
      (source_axis_direction_ne_zero _ hsource.1) hzero.1 hone.1,
      affine_slope_eq_zero (Scalar := _root_.MIPStarRE.QPBT.PauliScalar params)
        (source_axis_direction_ne_zero _ hsource.2) hzero.2 hone.2⟩
  · left
    have halpha := Ne.symm (not_or.mp hspecial).1
    have hbeta := Ne.symm (not_or.mp hspecial).2
    rw [← hcompat.2.1, ← hcompat.2.2.2.1, hcoordinate]
    simp [_root_.MIPStarRE.QPBT.coordinateDirection, halpha, hbeta]
