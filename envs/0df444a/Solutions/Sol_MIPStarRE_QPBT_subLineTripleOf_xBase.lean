-- Prove2me | solution 1 for MIPStarRE.QPBT.subLineTripleOf_xBase
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:03:55.801531+00:00
-- url     : https://prove2.me/submissions/f9dcb420-36ca-4b5d-b7fb-89d91c8852ca

-- Generated proof for MIPStarRE.QPBT.subLineTripleOf_xBase.
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
import Theorems.Thm_MIPStarRE_QPBT_lineRepMap_projX_directPointToPauli_lineRepMap
import Theorems.Thm_MIPStarRE_QPBT_projX_subLineExtDirection_mem_span

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





/-- The base of the extended line of a branch is the canonical representative
of the drawn point in the branch direction. -/
theorem subLineExtLine_base (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (kind : _root_.MIPStarRE.QPBT.LineKind)
    (k : Fin (2 * P.m + 2)) (w : _root_.MIPStarRE.QPBT.SubLineSamplingData P) :
    (_root_.MIPStarRE.QPBT.subLineExtLine P kind k w).base =
      _root_.MIPStarRE.QPBT.lineRepMap (_root_.MIPStarRE.QPBT.subLineExtDirection P kind k w.1.2) w.1.1 := by
  cases kind <;> rfl



/-- The direction of a source line of a branch is the branch source direction
at the coordinate index named by its seed. -/
theorem subLineSourceLine_direction (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (kind : _root_.MIPStarRE.QPBT.LineKind)
    (b : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) (s : _root_.MIPStarRE.QPBT.ScalarQ P.toLdParams)
    (d : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) :
    (_root_.MIPStarRE.QPBT.subLineSourceLine P kind b s d).direction =
      _root_.MIPStarRE.QPBT.subLineSourceDirection P kind (_root_.MIPStarRE.QPBT.chiIndex P.toLdParams s) d := by
  cases kind <;> rfl

/-- The base of a source line of a branch is the canonical representative of
its point block in its own direction. -/
theorem subLineSourceLine_base (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (kind : _root_.MIPStarRE.QPBT.LineKind)
    (b : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) (s : _root_.MIPStarRE.QPBT.ScalarQ P.toLdParams)
    (d : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) :
    (_root_.MIPStarRE.QPBT.subLineSourceLine P kind b s d).base =
      _root_.MIPStarRE.QPBT.lineRepMap (_root_.MIPStarRE.QPBT.subLineSourceDirection P kind (_root_.MIPStarRE.QPBT.chiIndex P.toLdParams s) d)
        b := by
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

















/-! ## Total mass and extended marginal -/









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
    (hx : _root_.MIPStarRE.QPBT.chiIndex P.toLdParams w.2.1 = _root_.MIPStarRE.QPBT.subLineXIndex P k) :
    (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k w).2.1.base =
      _root_.MIPStarRE.QPBT.lineRepMap (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k w).2.1.direction
        (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k w).1.base)) := by
  have hbridge := _root_.MIPStarRE.QPBT.lineRepMap_projX_directPointToPauli_lineRepMap P
    (_root_.MIPStarRE.QPBT.subLineExtDirection P kind k w.1.2) w.1.1
    (_root_.MIPStarRE.QPBT.subLineSourceDirection P kind (_root_.MIPStarRE.QPBT.subLineXIndex P k)
      (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P w.1.2)))
    (_root_.MIPStarRE.QPBT.projX_subLineExtDirection_mem_span P kind k w.1.2)
  have hbase : (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k w).2.1.base =
      _root_.MIPStarRE.QPBT.lineRepMap (_root_.MIPStarRE.QPBT.subLineSourceDirection P kind (_root_.MIPStarRE.QPBT.subLineXIndex P k)
        (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P w.1.2)))
        (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P w.1.1)) := by
    have h : (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k w).2.1.base =
        _root_.MIPStarRE.QPBT.lineRepMap (_root_.MIPStarRE.QPBT.subLineSourceDirection P kind
          (_root_.MIPStarRE.QPBT.chiIndex P.toLdParams w.2.1) (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P w.1.2)))
          (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P w.1.1)) :=
      _root_.MIPStarRE.QPBT.subLineSourceLine_base P kind _ w.2.1 _
    rw [h, hx]
  have hextbase : (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k w).1.base =
      _root_.MIPStarRE.QPBT.lineRepMap (_root_.MIPStarRE.QPBT.subLineExtDirection P kind k w.1.2) w.1.1 :=
    _root_.MIPStarRE.QPBT.subLineExtLine_base P kind k w
  rw [hbase, _root_.MIPStarRE.QPBT.subLineTripleOf_xDirection P kind k w hx, hextbase]
  exact hbridge.symm
