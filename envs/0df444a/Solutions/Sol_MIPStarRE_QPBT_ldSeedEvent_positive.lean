-- Prove2me | solution 1 for MIPStarRE.QPBT.ldSeedEvent_positive
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:55:47.154915+00:00
-- url     : https://prove2.me/submissions/39acb65e-e55f-44e8-abac-3854f0c9f15c

-- Generated proof for MIPStarRE.QPBT.ldSeedEvent_positive.
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
import Definitions.Def_QPBT_QPBT_Combining_Lines_SubLineSupport
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Mathlib

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

theorem solution (L : _root_.MIPStarRE.QPBT.LdParams) (i : Fin L.m) :
    0 < ∑ z ∈ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.LdSpace L)).support.filter
        (_root_.MIPStarRE.QPBT.ldSeedEvent L i),
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.LdSpace L)).weight z := by
  classical
  refine Finset.sum_pos'
    (fun a _ => (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.LdSpace L)).nonnegative a)
    ⟨(fun _ => _root_.MIPStarRE.QPBT.seedOfIndexResidue L i ⟨0, L.seedFiberCard_pos⟩),
      Finset.mem_filter.mpr ⟨by simp, ?_⟩, ?_⟩
  · show _root_.MIPStarRE.QPBT.chiIndex L (_root_.MIPStarRE.QPBT.seedOfIndexResidue L i ⟨0, L.seedFiberCard_pos⟩) = i
    exact _root_.MIPStarRE.QPBT.chiIndex_seedOfIndexResidue L i _
  · simp only [_root_.LIDT.MIPStarRE.LDT.uniformDistribution, _root_.LIDT.MIPStarRE.LDT.Distribution.uniformOnFinset_weight,
      Finset.mem_univ, if_true]
    positivity
