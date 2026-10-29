-- Prove2me | solution 1 for MIPStarRE.QPBT.aLinePointDist_eq_bind_restricted
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:08:26.560046+00:00
-- url     : https://prove2.me/submissions/1a5d9f96-904d-4033-ba9f-1800c312f6e2

-- Generated proof for MIPStarRE.QPBT.aLinePointDist_eq_bind_restricted.
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
import Definitions.Def_QPBT_QPBT_Games_CondLinear
import Definitions.Def_QPBT_QPBT_Games_DistributionAux
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_Distribution_bind_map
import Theorems.Thm_MIPStarRE_QPBT_Distribution_bind_uniform_restrict_eq
import Theorems.Thm_MIPStarRE_QPBT_clDistribution_seedEvent_mass

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# Uniform coordinate-index mixtures of the line-point laws

This module proves that the axis-parallel and diagonal line-point laws are the
uniform mixtures of their coordinate-index restrictions.  The identity rests on
the exact seed decomposition of `chiIndex`: the retained scalar seed is uniform,
so each of its `m` coordinate-index fibers carries mass `1 / m`, and every
line conditioning map keeps that seed.

## References

The mixture assertion is the opening sentence of blueprint
`lem:restricted-line-mixture-bounds`, formalizing the unlabelled observation at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1049-1051`.
The restricted laws are blueprint `def:ith-restricted-line`, paper lines
1038--1048.
-/



open scoped BigOperators

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT



/-! ## The uniform coordinate-index law of the retained seed -/



/-! ## The mass of a coordinate-index event -/



/-! ## The two source mixture identities -/

theorem solution (L : _root_.MIPStarRE.QPBT.LdParams) :
    _root_.MIPStarRE.QPBT.aLinePointDist L =
      _root_.MIPStarRE.QPBT.Distribution.bind (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin L.m))
        (_root_.MIPStarRE.QPBT.restrictedALineDist L) := by
  classical
  haveI : Nonempty (Fin L.m) :=
    Fin.pos_iff_nonempty.mp (lt_of_lt_of_le Nat.zero_lt_one L.hm)
  have hmix := _root_.MIPStarRE.QPBT.Distribution.bind_uniform_restrict_eq
    (_root_.MIPStarRE.QPBT.clDistribution (_root_.MIPStarRE.QPBT.ldALineCL L) (_root_.MIPStarRE.QPBT.ldPointCL L))
    (_root_.MIPStarRE.QPBT.restrictedLineSeedEvent L) (_root_.MIPStarRE.QPBT.restrictedALineSeedEvent_positive L)
    (fun i => by
      rw [_root_.MIPStarRE.QPBT.clDistribution_seedEvent_mass L i (_root_.MIPStarRE.QPBT.ldALineCL L) fun _ => rfl,
        Fintype.card_fin])
    (fun sample => ⟨_root_.MIPStarRE.QPBT.chiIndex L (_root_.MIPStarRE.QPBT.LdSpace.seed sample.1), rfl, fun i hi => hi.symm⟩)
  rw [_root_.MIPStarRE.QPBT.aLinePointDist, ← hmix, _root_.MIPStarRE.QPBT.Distribution.bind_map]
  rfl
