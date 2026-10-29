-- Prove2me | solution 1 for MIPStarRE.QPBT.lineRepMap_projX_subLineExtLine_point
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:03:55.21245+00:00
-- url     : https://prove2.me/submissions/5b609805-afc1-4515-9d52-5936cc07d3eb

-- Generated proof for MIPStarRE.QPBT.lineRepMap_projX_subLineExtLine_point.
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
import Definitions.Def_QPBT_QPBT_Combining_Lines_SubLineBranch
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_lineRepMap_projX_directPointToPauli_lineRepMap
import Theorems.Thm_MIPStarRE_QPBT_projX_subLineExtDirection_mem_span

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# The projected marginals of the sub-line law

This module identifies the two projected point marginals of the sub-line law
of `lem:qld-sublines` as mixtures of the restricted product laws.  The two
source lines of a sampled triple depend on the drawn extended point only
through the canonical representatives of its two source blocks, and those
representatives are unchanged when the drawn point is replaced by any point of
the extended line; a uniform point of the extended line through a uniform
point is a uniform point, so the drawn point may be replaced throughout by the
point that is finally retained.  The six generating blocks of the resulting
law -- the two source point blocks, the two scalar seeds and the two source
direction blocks -- are then regrouped into the two restricted product laws
carried by the two indices of the branch.

## References

The identification is the last step of the proof of `lem:qld-sublines` in
blueprint `lem:qld-sublines`, whose source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`.
The restricted laws are `def:ith-restricted-line`, blueprint lines
1209--1228, paper lines 1038--1048.
-/



open scoped BigOperators

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT



/-! ## Source lines depend on the point block only through its representative -/

theorem solution (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (kind : _root_.MIPStarRE.QPBT.LineKind) (k : Fin (2 * P.m + 2))
    (x e : Fin (2 * P.m + 2) → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd)
    (t : _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd) :
    _root_.MIPStarRE.QPBT.lineRepMap
        (_root_.MIPStarRE.QPBT.subLineSourceDirection P kind (_root_.MIPStarRE.QPBT.subLineXIndex P k)
          (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P e)))
        (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P
          (_root_.MIPStarRE.QPBT.lineRepMap (_root_.MIPStarRE.QPBT.subLineExtDirection P kind k e) x +
            t • _root_.MIPStarRE.QPBT.subLineExtDirection P kind k e))) =
      _root_.MIPStarRE.QPBT.lineRepMap
        (_root_.MIPStarRE.QPBT.subLineSourceDirection P kind (_root_.MIPStarRE.QPBT.subLineXIndex P k)
          (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P e)))
        (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P x)) := by
  have hspan := _root_.MIPStarRE.QPBT.projX_subLineExtDirection_mem_span P kind k e
  have hrep : _root_.MIPStarRE.QPBT.lineRepMap (_root_.MIPStarRE.QPBT.subLineExtDirection P kind k e)
      (_root_.MIPStarRE.QPBT.lineRepMap (_root_.MIPStarRE.QPBT.subLineExtDirection P kind k e) x +
        t • _root_.MIPStarRE.QPBT.subLineExtDirection P kind k e) =
      _root_.MIPStarRE.QPBT.lineRepMap (_root_.MIPStarRE.QPBT.subLineExtDirection P kind k e) x := by
    rw [_root_.MIPStarRE.QPBT.lineRepMap_add_smul]
    apply _root_.MIPStarRE.QPBT.lineRepMap_apply_self
  have h1 := _root_.MIPStarRE.QPBT.lineRepMap_projX_directPointToPauli_lineRepMap P
    (_root_.MIPStarRE.QPBT.subLineExtDirection P kind k e)
    (_root_.MIPStarRE.QPBT.lineRepMap (_root_.MIPStarRE.QPBT.subLineExtDirection P kind k e) x +
      t • _root_.MIPStarRE.QPBT.subLineExtDirection P kind k e)
    (_root_.MIPStarRE.QPBT.subLineSourceDirection P kind (_root_.MIPStarRE.QPBT.subLineXIndex P k)
      (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P e))) hspan
  have h2 := _root_.MIPStarRE.QPBT.lineRepMap_projX_directPointToPauli_lineRepMap P
    (_root_.MIPStarRE.QPBT.subLineExtDirection P kind k e) x
    (_root_.MIPStarRE.QPBT.subLineSourceDirection P kind (_root_.MIPStarRE.QPBT.subLineXIndex P k)
      (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P e))) hspan
  rw [← h1, ← h2, hrep]
