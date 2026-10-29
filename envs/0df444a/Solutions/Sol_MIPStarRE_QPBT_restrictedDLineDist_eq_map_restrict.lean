-- Prove2me | solution 1 for MIPStarRE.QPBT.restrictedDLineDist_eq_map_restrict
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:38:59.220924+00:00
-- url     : https://prove2.me/submissions/2d502ac6-2e5a-487b-8eb2-2b92a24ecc6b

-- Generated proof for MIPStarRE.QPBT.restrictedDLineDist_eq_map_restrict.
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
import Definitions.Def_QPBT_QPBT_Combining_Defs
import Definitions.Def_QPBT_QPBT_Combining_Lines_SubLineSupport
import Definitions.Def_QPBT_QPBT_Games_CondLinear
import Definitions.Def_QPBT_QPBT_Games_DistributionAux
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_Distribution_restrict_map
import Theorems.Thm_MIPStarRE_QPBT_dLineDescOf_ldDLineCL
import Theorems.Thm_MIPStarRE_QPBT_ldSeedEvent_positive

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# Generating laws of the restricted line-point distributions

This module rewrites the two restricted line-point laws of
`def:ith-restricted-line` as push-forwards of a single uniformly sampled
low-degree vector conditioned on the coordinate-index fiber of its retained
scalar seed.  In that form the point block, the seed and the direction block
of the sampled vector are visibly the independent generating data of the
restricted law, which is the description used by the sampling procedure of the
sub-line lemma: there the projected pairs are built either from a direction
block inherited from the extended line or from freshly sampled data, and each
is asserted to follow a restricted law.

## References

The generating descriptions support `lem:qld-sublines` in
blueprint `lem:qld-sublines`, whose source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`.
The restricted laws themselves are `def:ith-restricted-line`, blueprint lines
1209--1228, paper lines 1038--1048.
-/



open scoped BigOperators

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT



/-! ## The coordinate-index event on a single uniform vector -/







/-! ## Canonical representatives are unchanged by the conditioning maps -/









/-! ## Generating laws of the restricted line-point distributions -/

theorem solution (L : _root_.MIPStarRE.QPBT.LdParams) (i : Fin L.m) :
    _root_.MIPStarRE.QPBT.restrictedDLineDist L i =
      (_root_.MIPStarRE.QPBT.Distribution.restrict (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.LdSpace L))
          (_root_.MIPStarRE.QPBT.ldSeedEvent L i) (_root_.MIPStarRE.QPBT.ldSeedEvent_positive L i)).map
        (fun z => (_root_.MIPStarRE.QPBT.dLineDescOf L z, _root_.MIPStarRE.QPBT.LdSpace.point z)) := by
  classical
  have hcomp :
      (fun z : _root_.MIPStarRE.QPBT.LdSpace L =>
          (_root_.MIPStarRE.QPBT.dLineDescOf L (_root_.MIPStarRE.QPBT.ldDLineCL L z), _root_.MIPStarRE.QPBT.LdSpace.point (_root_.MIPStarRE.QPBT.ldPointCL L z))) =
        fun z : _root_.MIPStarRE.QPBT.LdSpace L => (_root_.MIPStarRE.QPBT.dLineDescOf L z, _root_.MIPStarRE.QPBT.LdSpace.point z) := by
    funext z
    rw [_root_.MIPStarRE.QPBT.dLineDescOf_ldDLineCL]
    rfl
  have hpos :
      0 < ∑ sample ∈
          ((_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.LdSpace L)).map
            (fun z => (_root_.MIPStarRE.QPBT.ldDLineCL L z, _root_.MIPStarRE.QPBT.ldPointCL L z))).support.filter
              (_root_.MIPStarRE.QPBT.restrictedLineSeedEvent L i),
        ((_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.LdSpace L)).map
          (fun z => (_root_.MIPStarRE.QPBT.ldDLineCL L z, _root_.MIPStarRE.QPBT.ldPointCL L z))).weight sample := by
    simpa only [_root_.MIPStarRE.QPBT.clDistribution] using _root_.MIPStarRE.QPBT.restrictedDLineSeedEvent_positive L i
  unfold _root_.MIPStarRE.QPBT.restrictedDLineDist _root_.MIPStarRE.QPBT.restrictedDLinePreDist _root_.MIPStarRE.QPBT.clDistribution
  rw [_root_.MIPStarRE.QPBT.Distribution.restrict_map (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.LdSpace L))
      (fun z => (_root_.MIPStarRE.QPBT.ldDLineCL L z, _root_.MIPStarRE.QPBT.ldPointCL L z))
      (_root_.MIPStarRE.QPBT.restrictedLineSeedEvent L i) (_root_.MIPStarRE.QPBT.ldSeedEvent L i) (fun _ => Iff.rfl)
      hpos (_root_.MIPStarRE.QPBT.ldSeedEvent_positive L i),
    _root_.MIPStarRE.QPBT.Distribution.map_map]
  exact congrArg _ hcomp
