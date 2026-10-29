-- Prove2me | solution 1 for MIPStarRE.QPBT.exists_samplingData_of_mem_subLineDist_support
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:55:47.238317+00:00
-- url     : https://prove2.me/submissions/90ef9874-916b-48d8-8d28-585cf4d78e58

-- Generated proof for MIPStarRE.QPBT.exists_samplingData_of_mem_subLineDist_support.
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
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_Lines_SubLineBranch
import Definitions.Def_QPBT_QPBT_Combining_Lines_SubLineConstruct
import Definitions.Def_QPBT_QPBT_Combining_Lines_SubLineSeed
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Games_DistributionAux
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace MIPStarRE.QPBT
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

theorem solution (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    {sample : _root_.MIPStarRE.QPBT.SubLineTriple P} (hsample : sample ∈ (_root_.MIPStarRE.QPBT.subLineDist P).support) :
    ∃ (kind : _root_.MIPStarRE.QPBT.LineKind) (k : Fin (2 * P.m + 2)) (w : _root_.MIPStarRE.QPBT.SubLineSamplingData P),
      _root_.MIPStarRE.QPBT.chiIndex P.toLdParams w.2.1 = _root_.MIPStarRE.QPBT.subLineXIndex P k ∧
        _root_.MIPStarRE.QPBT.chiIndex P.toLdParams w.2.2 = _root_.MIPStarRE.QPBT.subLineZIndex P k ∧
        sample = _root_.MIPStarRE.QPBT.subLineTripleOf P kind k w := by
  classical
  have hbind : sample ∈ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin 2)).support.biUnion
      (fun c => (![_root_.MIPStarRE.QPBT.subLineBranchDist P .axis,
        _root_.MIPStarRE.QPBT.subLineBranchDist P .diagonal] c).support) := hsample
  obtain ⟨c, -, hc⟩ := Finset.mem_biUnion.mp hbind
  obtain ⟨kind, hkind⟩ : ∃ kind : _root_.MIPStarRE.QPBT.LineKind,
      sample ∈ (_root_.MIPStarRE.QPBT.subLineBranchDist P kind).support := by
    fin_cases c
    · exact ⟨.axis, by simpa using hc⟩
    · exact ⟨.diagonal, by simpa using hc⟩
  obtain ⟨kw, hkw, hkw'⟩ := Finset.mem_image.mp hkind
  obtain ⟨k, -, hk⟩ := Finset.mem_biUnion.mp
    (show kw ∈ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin (2 * P.m + 2))).support.biUnion
      (fun k => ((_root_.MIPStarRE.QPBT.Distribution.prod (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.SubLinePointDir P))
        (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.subLineSeedDist P (_root_.MIPStarRE.QPBT.subLineXIndex P k))
          (_root_.MIPStarRE.QPBT.subLineSeedDist P (_root_.MIPStarRE.QPBT.subLineZIndex P k)))).map
        (fun w => (k, w))).support) from hkw)
  obtain ⟨w, hw, hw'⟩ := Finset.mem_image.mp hk
  obtain ⟨-, hseeds⟩ := Finset.mem_product.mp hw
  obtain ⟨hsx, hsz⟩ := Finset.mem_product.mp hseeds
  have hx : _root_.MIPStarRE.QPBT.chiIndex P.toLdParams w.2.1 = _root_.MIPStarRE.QPBT.subLineXIndex P k :=
    (Finset.mem_filter.mp hsx).2
  have hz : _root_.MIPStarRE.QPBT.chiIndex P.toLdParams w.2.2 = _root_.MIPStarRE.QPBT.subLineZIndex P k :=
    (Finset.mem_filter.mp hsz).2
  refine ⟨kind, k, w, hx, hz, ?_⟩
  rw [← hkw', ← hw']
