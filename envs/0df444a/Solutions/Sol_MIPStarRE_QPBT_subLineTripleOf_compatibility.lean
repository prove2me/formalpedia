-- Prove2me | solution 1 for MIPStarRE.QPBT.subLineTripleOf_compatibility
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:08:28.488734+00:00
-- url     : https://prove2.me/submissions/4464d81e-c457-44bc-a348-953767f889e1

-- Generated proof for MIPStarRE.QPBT.subLineTripleOf_compatibility.
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
import Definitions.Def_QPBT_QPBT_Combining_Lines_SubLineConstruct
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_projX_subLineExtDirection_mem_span
import Theorems.Thm_MIPStarRE_QPBT_projZ_subLineExtDirection_mem_span
import Theorems.Thm_MIPStarRE_QPBT_subLineTripleOf_xBase
import Theorems.Thm_MIPStarRE_QPBT_subLineTripleOf_zBase

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/Lines/SubLineConstruct.lean. -/
/-!
# The sampling procedure of the sub-line lemma

This module carries out the sampling procedure of `lem:qld-sublines`.  A line
kind is drawn from the two kinds, an extended coordinate and an extended point
and direction are drawn uniformly, and two scalar seeds are drawn
independently in the coordinate-index fibers of the two coordinates that the
two source lines must carry.  The sampled triple consists of the axis or
diagonal line of the extended sample together with the two source lines
decoded from the two coordinate blocks of the extended point and direction and
from the two seeds.

The module records the elementary evaluations of that triple, the description
of the support of the resulting law, the three pointwise properties of a
sampled triple -- incidence of the two source blocks, compatibility of the
affine data, and closure of the axis branch -- and the identification of its
extended-line marginal.

## References

The construction is the proof of `lem:qld-sublines` in
blueprint `lem:qld-sublines`, whose source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`.
The restricted laws are `def:ith-restricted-line`, blueprint lines
1209--1228, paper lines 1038--1048.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

noncomputable section

/-! ## The auxiliary randomness of one branch -/













/-! ## The sampled triple -/













/-! ## Elementary evaluations of the sampled triple -/



/-- The direction of the extended line of a branch is the branch direction. -/
theorem subLineExtLine_direction (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (kind : _root_.MIPStarRE.QPBT.LineKind)
    (k : Fin (2 * P.m + 2)) (w : _root_.MIPStarRE.QPBT.SubLineSamplingData P) :
    (_root_.MIPStarRE.QPBT.subLineExtLine P kind k w).direction =
      _root_.MIPStarRE.QPBT.subLineExtDirection P kind k w.1.2 := by
  cases kind <;> rfl





/-- The direction of a source line of a branch is the branch source direction
at the coordinate index named by its seed. -/
theorem subLineSourceLine_direction (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (kind : _root_.MIPStarRE.QPBT.LineKind)
    (b : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) (s : _root_.MIPStarRE.QPBT.ScalarQ P.toLdParams)
    (d : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) :
    (_root_.MIPStarRE.QPBT.subLineSourceLine P kind b s d).direction =
      _root_.MIPStarRE.QPBT.subLineSourceDirection P kind (_root_.MIPStarRE.QPBT.chiIndex P.toLdParams s) d := by
  cases kind <;> rfl



/-! ## The support of the sub-line law -/



/-! ## Pointwise properties of a sampled triple -/

/-- The direction of the source `X` line of a sampled triple is the branch
source direction at the coordinate carried by that line. -/
theorem subLineTripleOf_xDirection (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (kind : _root_.MIPStarRE.QPBT.LineKind)
    (k : Fin (2 * P.m + 2)) (w : _root_.MIPStarRE.QPBT.SubLineSamplingData P)
    (hx : _root_.MIPStarRE.QPBT.chiIndex P.toLdParams w.2.1 = _root_.MIPStarRE.QPBT.subLineXIndex P k) :
    (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k w).2.1.direction =
      _root_.MIPStarRE.QPBT.subLineSourceDirection P kind (_root_.MIPStarRE.QPBT.subLineXIndex P k)
        (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P w.1.2)) := by
  have h : (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k w).2.1.direction =
      _root_.MIPStarRE.QPBT.subLineSourceDirection P kind (_root_.MIPStarRE.QPBT.chiIndex P.toLdParams w.2.1)
        (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P w.1.2)) :=
    _root_.MIPStarRE.QPBT.subLineSourceLine_direction P kind _ w.2.1 _
  rw [h, hx]

/-- The direction of the source `Z` line of a sampled triple is the branch
source direction at the coordinate carried by that line. -/
theorem subLineTripleOf_zDirection (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (kind : _root_.MIPStarRE.QPBT.LineKind)
    (k : Fin (2 * P.m + 2)) (w : _root_.MIPStarRE.QPBT.SubLineSamplingData P)
    (hz : _root_.MIPStarRE.QPBT.chiIndex P.toLdParams w.2.2 = _root_.MIPStarRE.QPBT.subLineZIndex P k) :
    (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k w).2.2.direction =
      _root_.MIPStarRE.QPBT.subLineSourceDirection P kind (_root_.MIPStarRE.QPBT.subLineZIndex P k)
        (_root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P w.1.2)) := by
  have h : (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k w).2.2.direction =
      _root_.MIPStarRE.QPBT.subLineSourceDirection P kind (_root_.MIPStarRE.QPBT.chiIndex P.toLdParams w.2.2)
        (_root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P w.1.2)) :=
    _root_.MIPStarRE.QPBT.subLineSourceLine_direction P kind _ w.2.2 _
  rw [h, hz]

/-- The `X` block of the direction of the extended line of a sampled triple
lies in the line spanned by the direction of its source `X` line. -/
theorem subLineTripleOf_xSpan (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (kind : _root_.MIPStarRE.QPBT.LineKind)
    (k : Fin (2 * P.m + 2)) (w : _root_.MIPStarRE.QPBT.SubLineSamplingData P)
    (hx : _root_.MIPStarRE.QPBT.chiIndex P.toLdParams w.2.1 = _root_.MIPStarRE.QPBT.subLineXIndex P k) :
    _root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k w).1.direction) ∈
      Submodule.span (_root_.MIPStarRE.QPBT.PauliScalar P)
        ({(_root_.MIPStarRE.QPBT.subLineTripleOf P kind k w).2.1.direction} :
          Set (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)) := by
  have hext : (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k w).1.direction =
      _root_.MIPStarRE.QPBT.subLineExtDirection P kind k w.1.2 := _root_.MIPStarRE.QPBT.subLineExtLine_direction P kind k w
  rw [_root_.MIPStarRE.QPBT.subLineTripleOf_xDirection P kind k w hx, hext]
  exact _root_.MIPStarRE.QPBT.projX_subLineExtDirection_mem_span P kind k w.1.2

/-- The `Z` block of the direction of the extended line of a sampled triple
lies in the line spanned by the direction of its source `Z` line. -/
theorem subLineTripleOf_zSpan (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (kind : _root_.MIPStarRE.QPBT.LineKind)
    (k : Fin (2 * P.m + 2)) (w : _root_.MIPStarRE.QPBT.SubLineSamplingData P)
    (hz : _root_.MIPStarRE.QPBT.chiIndex P.toLdParams w.2.2 = _root_.MIPStarRE.QPBT.subLineZIndex P k) :
    _root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k w).1.direction) ∈
      Submodule.span (_root_.MIPStarRE.QPBT.PauliScalar P)
        ({(_root_.MIPStarRE.QPBT.subLineTripleOf P kind k w).2.2.direction} :
          Set (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)) := by
  have hext : (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k w).1.direction =
      _root_.MIPStarRE.QPBT.subLineExtDirection P kind k w.1.2 := _root_.MIPStarRE.QPBT.subLineExtLine_direction P kind k w
  rw [_root_.MIPStarRE.QPBT.subLineTripleOf_zDirection P kind k w hz, hext]
  exact _root_.MIPStarRE.QPBT.projZ_subLineExtDirection_mem_span P kind k w.1.2











/-! ## Total mass and extended marginal -/









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

/-- The `X` block of a scalar multiple of an extended point is the scalar
multiple of the block.  Blueprint `def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem projX_smul {K : Type*} [Monoid K] {m : ℕ} (t : K)
    (u : Fin (2 * m + 2) → K) :
    _root_.MIPStarRE.QPBT.projX (t • u) = t • _root_.MIPStarRE.QPBT.projX u := rfl

/-- The `Z` block of a scalar multiple of an extended point is the scalar
multiple of the block.  Blueprint `def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem projZ_smul {K : Type*} [Monoid K] {m : ℕ} (t : K)
    (u : Fin (2 * m + 2) → K) :
    _root_.MIPStarRE.QPBT.projZ (t • u) = t • _root_.MIPStarRE.QPBT.projZ u := rfl

/-! ## The coordinate blocks of an extended point -/















/-! ## Transport to the source scalar field -/





/-! ## The blocks of an extended direct sample -/



/-! ## Compatibility data read off the coordinate blocks -/

/-- An extended line is compatible with two source lines as soon as each of
its two point blocks is an affine reparameterization of the corresponding
source line: the base block is a point of the source line and the direction
block is a multiple of the source direction.  The two scalar coordinates of
the compatibility data are the `alpha` and `beta` coordinates of the extended
base and direction.  This supplies the domain condition preceding Equation
`eq:combine-lines` in blueprint
`def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem isCombineLineCompatible_of_blocks {K : Type*} [Field K] {m : ℕ}
    (u v : Fin (2 * m + 2) → K) (uX vX uZ vZ : Fin m → K) (aX bX aZ bZ : K)
    (hX : _root_.MIPStarRE.QPBT.projX u = uX + aX • vX) (hXv : _root_.MIPStarRE.QPBT.projX v = bX • vX)
    (hZ : _root_.MIPStarRE.QPBT.projZ u = uZ + aZ • vZ) (hZv : _root_.MIPStarRE.QPBT.projZ v = bZ • vZ) :
    _root_.MIPStarRE.QPBT.IsCombineLineCompatible u v uX vX uZ vZ aX bX aZ bZ
      (u (_root_.MIPStarRE.QPBT.alphaVar m)) (v (_root_.MIPStarRE.QPBT.alphaVar m)) (u (_root_.MIPStarRE.QPBT.betaVar m)) (v (_root_.MIPStarRE.QPBT.betaVar m)) := by
  refine ⟨rfl, rfl, rfl, rfl, fun t => ⟨?_, ?_⟩⟩
  · rw [_root_.MIPStarRE.QPBT.projX_add, _root_.MIPStarRE.QPBT.projX_smul, hX, hXv]
    module
  · rw [_root_.MIPStarRE.QPBT.projZ_add, _root_.MIPStarRE.QPBT.projZ_smul, hZ, hZv]
    module



end

end MIPStarRE.QPBT

/-!
# The sampling procedure of the sub-line lemma

This module carries out the sampling procedure of `lem:qld-sublines`.  A line
kind is drawn from the two kinds, an extended coordinate and an extended point
and direction are drawn uniformly, and two scalar seeds are drawn
independently in the coordinate-index fibers of the two coordinates that the
two source lines must carry.  The sampled triple consists of the axis or
diagonal line of the extended sample together with the two source lines
decoded from the two coordinate blocks of the extended point and direction and
from the two seeds.

The module records the elementary evaluations of that triple, the description
of the support of the resulting law, the three pointwise properties of a
sampled triple -- incidence of the two source blocks, compatibility of the
affine data, and closure of the axis branch -- and the identification of its
extended-line marginal.

## References

The construction is the proof of `lem:qld-sublines` in
blueprint `lem:qld-sublines`, whose source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`.
The restricted laws are `def:ith-restricted-line`, blueprint lines
1209--1228, paper lines 1038--1048.
-/



open scoped BigOperators

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT



/-! ## The auxiliary randomness of one branch -/













/-! ## The sampled triple -/













/-! ## Elementary evaluations of the sampled triple -/













/-! ## The support of the sub-line law -/



/-! ## Pointwise properties of a sampled triple -/

theorem solution (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (kind : _root_.MIPStarRE.QPBT.LineKind)
    (k : Fin (2 * P.m + 2)) (w : _root_.MIPStarRE.QPBT.SubLineSamplingData P)
    (hx : _root_.MIPStarRE.QPBT.chiIndex P.toLdParams w.2.1 = _root_.MIPStarRE.QPBT.subLineXIndex P k)
    (hz : _root_.MIPStarRE.QPBT.chiIndex P.toLdParams w.2.2 = _root_.MIPStarRE.QPBT.subLineZIndex P k) :
    ∃ aX bX aZ bZ uAlpha vAlpha uBeta vBeta : _root_.MIPStarRE.QPBT.PauliScalar P,
      _root_.MIPStarRE.QPBT.IsCombineLineCompatible
        (_root_.MIPStarRE.QPBT.directPointToPauli P (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k w).1.base)
        (_root_.MIPStarRE.QPBT.directPointToPauli P (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k w).1.direction)
        (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k w).2.1.base
        (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k w).2.1.direction
        (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k w).2.2.base
        (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k w).2.2.direction
        aX bX aZ bZ uAlpha vAlpha uBeta vBeta := by
  obtain ⟨aX, haX⟩ := Submodule.mem_span_singleton.mp
    (_root_.MIPStarRE.QPBT.sub_lineRepMap_mem_span (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k w).2.1.direction
      (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k w).1.base)))
  obtain ⟨aZ, haZ⟩ := Submodule.mem_span_singleton.mp
    (_root_.MIPStarRE.QPBT.sub_lineRepMap_mem_span (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k w).2.2.direction
      (_root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k w).1.base)))
  obtain ⟨bX, hbX⟩ := Submodule.mem_span_singleton.mp
    (_root_.MIPStarRE.QPBT.subLineTripleOf_xSpan P kind k w hx)
  obtain ⟨bZ, hbZ⟩ := Submodule.mem_span_singleton.mp
    (_root_.MIPStarRE.QPBT.subLineTripleOf_zSpan P kind k w hz)
  have hXblock :
      _root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k w).1.base) =
        (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k w).2.1.base +
          aX • (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k w).2.1.direction := by
    rw [_root_.MIPStarRE.QPBT.subLineTripleOf_xBase P kind k w hx, haX]
    abel
  have hZblock :
      _root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k w).1.base) =
        (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k w).2.2.base +
          aZ • (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k w).2.2.direction := by
    rw [_root_.MIPStarRE.QPBT.subLineTripleOf_zBase P kind k w hz, haZ]
    abel
  have hcompat := _root_.MIPStarRE.QPBT.isCombineLineCompatible_of_blocks
    (_root_.MIPStarRE.QPBT.directPointToPauli P (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k w).1.base)
    (_root_.MIPStarRE.QPBT.directPointToPauli P (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k w).1.direction)
    (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k w).2.1.base
    (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k w).2.1.direction
    (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k w).2.2.base
    (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k w).2.2.direction
    aX bX aZ bZ hXblock hbX.symm hZblock hbZ.symm
  exact ⟨aX, bX, aZ, bZ, _, _, _, _, hcompat⟩
