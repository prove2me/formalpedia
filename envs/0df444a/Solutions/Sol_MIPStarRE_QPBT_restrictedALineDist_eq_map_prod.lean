-- Prove2me | solution 1 for MIPStarRE.QPBT.restrictedALineDist_eq_map_prod
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:42:40.060995+00:00
-- url     : https://prove2.me/submissions/5fcc84da-3cd2-420e-9097-66dd1d500336

-- Generated proof for MIPStarRE.QPBT.restrictedALineDist_eq_map_prod.
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
import Definitions.Def_QPBT_QPBT_Combining_Lines_SubLineBlocks
import Definitions.Def_QPBT_QPBT_Combining_Lines_SubLineSupport
import Definitions.Def_QPBT_QPBT_Games_DistributionAux
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_ldSeedEvent_positive
import Theorems.Thm_MIPStarRE_QPBT_restrict_uniform_ldSeedEvent_map_block
import Theorems.Thm_MIPStarRE_QPBT_restrictedALineDist_eq_map_restrict

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# Independent blocks of the restricted line-point laws

This module isolates the independent generating blocks of the restricted
line-point laws used by the sampling procedure of the sub-line lemma.  A
uniformly sampled low-degree vector splits into a point block and a
seed-direction block; the coordinate-index event constrains only the second
block, so conditioning on it leaves the point block uniform and independent.
The conditioned seed-direction block is the fresh diagonal direction pair of
the sub-line construction, and the uniform mixture of those pairs over the
coordinate index is the unconditioned law.

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



/-! ## The block decomposition of an ambient low-degree vector -/











/-! ## Fresh diagonal direction pairs -/







/-! ## Independence of the point block under the coordinate-index event -/



/-! ## Generating form of the restricted line-point laws -/

theorem solution (L : _root_.MIPStarRE.QPBT.LdParams) (i : Fin L.m) :
    _root_.MIPStarRE.QPBT.restrictedALineDist L i =
      (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L))
          (_root_.MIPStarRE.QPBT.freshDiagonalPairDist L i)).map
        (fun w => (_root_.MIPStarRE.QPBT.aLineDescOfBlock L w, w.1)) := by
  classical
  have hfun : (fun z : _root_.MIPStarRE.QPBT.LdSpace L =>
        (_root_.MIPStarRE.QPBT.aLineDescOfBlock L (_root_.MIPStarRE.QPBT.ldSpaceBlockEquiv L z),
          (_root_.MIPStarRE.QPBT.ldSpaceBlockEquiv L z).1)) =
      fun z : _root_.MIPStarRE.QPBT.LdSpace L => (_root_.MIPStarRE.QPBT.aLineDescOf L z, _root_.MIPStarRE.QPBT.LdSpace.point z) := by
    funext z
    have h : (_root_.MIPStarRE.QPBT.ldSpaceBlockEquiv L).symm (_root_.MIPStarRE.QPBT.ldSpaceBlockEquiv L z) = z :=
      (_root_.MIPStarRE.QPBT.ldSpaceBlockEquiv L).symm_apply_apply z
    show (_root_.MIPStarRE.QPBT.aLineDescOf L ((_root_.MIPStarRE.QPBT.ldSpaceBlockEquiv L).symm (_root_.MIPStarRE.QPBT.ldSpaceBlockEquiv L z)),
        _root_.MIPStarRE.QPBT.LdSpace.point z) = (_root_.MIPStarRE.QPBT.aLineDescOf L z, _root_.MIPStarRE.QPBT.LdSpace.point z)
    rw [h]
  rw [_root_.MIPStarRE.QPBT.restrictedALineDist_eq_map_restrict,
    ← _root_.MIPStarRE.QPBT.restrict_uniform_ldSeedEvent_map_block, _root_.MIPStarRE.QPBT.Distribution.map_map, hfun]
