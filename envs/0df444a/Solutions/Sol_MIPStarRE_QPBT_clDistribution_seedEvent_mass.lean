-- Prove2me | solution 1 for MIPStarRE.QPBT.clDistribution_seedEvent_mass
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:04:46.078697+00:00
-- url     : https://prove2.me/submissions/b72f954e-e062-4351-a322-cbfa606e4403

-- Generated proof for MIPStarRE.QPBT.clDistribution_seedEvent_mass.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
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
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGameMeasurements
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_uniformDistribution_map_ldSeed

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/Lines/RestrictedMixture.lean. -/
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

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

noncomputable section

/-! ## The uniform coordinate-index law of the retained seed -/

/-- The coordinate index of the retained seed of a uniformly sampled low-degree
vector is uniform.  Formalization-only auxiliary for blueprint
`def:ith-restricted-line`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1038-1048`. -/
theorem uniformDistribution_map_chiIndex_ldSeed (L : _root_.MIPStarRE.QPBT.LdParams) :
    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.LdSpace L)).map
        (fun z : _root_.MIPStarRE.QPBT.LdSpace L => _root_.MIPStarRE.QPBT.chiIndex L z.seed) =
      _root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin L.m) := by
  classical
  haveI : Nonempty (_root_.MIPStarRE.QPBT.ScalarQ L) := ⟨0⟩
  haveI : Nonempty (Fin L.m) :=
    Fin.pos_iff_nonempty.mp (lt_of_lt_of_le Nat.zero_lt_one L.hm)
  rw [← _root_.MIPStarRE.QPBT.Distribution.map_map (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.LdSpace L))
      (fun z : _root_.MIPStarRE.QPBT.LdSpace L => _root_.MIPStarRE.QPBT.LdSpace.seed z) (_root_.MIPStarRE.QPBT.chiIndex L),
    _root_.MIPStarRE.QPBT.uniformDistribution_map_ldSeed, _root_.MIPStarRE.QPBT.uniformDistribution_map_chiIndex]

/-! ## The mass of a coordinate-index event -/



/-! ## The two source mixture identities -/





end

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

theorem solution (L : _root_.MIPStarRE.QPBT.LdParams) (i : Fin L.m)
    (CL : _root_.MIPStarRE.QPBT.LdSpace L → _root_.MIPStarRE.QPBT.LdSpace L)
    (hseed : ∀ z : _root_.MIPStarRE.QPBT.LdSpace L, (CL z).seed = z.seed) :
    ∑ sample ∈
        (_root_.MIPStarRE.QPBT.clDistribution CL (_root_.MIPStarRE.QPBT.ldPointCL L)).support.filter
          (_root_.MIPStarRE.QPBT.restrictedLineSeedEvent L i),
      (_root_.MIPStarRE.QPBT.clDistribution CL (_root_.MIPStarRE.QPBT.ldPointCL L)).weight sample = 1 / (L.m : ℝ) := by
  classical
  haveI : Nonempty (Fin L.m) :=
    Fin.pos_iff_nonempty.mp (lt_of_lt_of_le Nat.zero_lt_one L.hm)
  rw [_root_.MIPStarRE.QPBT.Distribution.sum_filter_weight_eq_avgOver]
  unfold _root_.MIPStarRE.QPBT.clDistribution
  rw [_root_.LIDT.MIPStarRE.LDT.Distribution.avgOver_map]
  have hpoint : ∀ z : _root_.MIPStarRE.QPBT.LdSpace L,
      (if _root_.MIPStarRE.QPBT.restrictedLineSeedEvent L i (CL z, _root_.MIPStarRE.QPBT.ldPointCL L z) then (1 : ℝ)
        else 0) = if _root_.MIPStarRE.QPBT.chiIndex L z.seed = i then 1 else 0 := by
    intro z
    by_cases h : _root_.MIPStarRE.QPBT.chiIndex L z.seed = i
    · rw [if_pos h, if_pos]
      change _root_.MIPStarRE.QPBT.chiIndex L (_root_.MIPStarRE.QPBT.LdSpace.seed (CL z)) = i
      rw [hseed z]
      exact h
    · rw [if_neg h, if_neg]
      change ¬ _root_.MIPStarRE.QPBT.chiIndex L (_root_.MIPStarRE.QPBT.LdSpace.seed (CL z)) = i
      rw [hseed z]
      exact h
  rw [_root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ hpoint,
    show (fun z : _root_.MIPStarRE.QPBT.LdSpace L => if _root_.MIPStarRE.QPBT.chiIndex L z.seed = i then (1 : ℝ) else 0) =
        fun z : _root_.MIPStarRE.QPBT.LdSpace L => (fun j : Fin L.m => if j = i then (1 : ℝ) else 0)
          (_root_.MIPStarRE.QPBT.chiIndex L z.seed) from rfl,
    ← _root_.LIDT.MIPStarRE.LDT.Distribution.avgOver_map (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.LdSpace L))
      (fun z : _root_.MIPStarRE.QPBT.LdSpace L => _root_.MIPStarRE.QPBT.chiIndex L z.seed)
      (fun j : Fin L.m => if j = i then (1 : ℝ) else 0),
    _root_.MIPStarRE.QPBT.uniformDistribution_map_chiIndex_ldSeed]
  unfold _root_.LIDT.MIPStarRE.LDT.avgOver
  simp [_root_.MIPStarRE.QPBT.uniformDistribution_weight_apply, mul_ite]
