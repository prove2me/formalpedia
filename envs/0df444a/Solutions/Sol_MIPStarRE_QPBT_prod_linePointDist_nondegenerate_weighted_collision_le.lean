-- Prove2me | solution 1 for MIPStarRE.QPBT.prod_linePointDist_nondegenerate_weighted_collision_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:38:59.520651+00:00
-- url     : https://prove2.me/submissions/9ac613b9-346c-4aba-bfb7-e514e536703f

-- Generated proof for MIPStarRE.QPBT.prod_linePointDist_nondegenerate_weighted_collision_le.
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
import Definitions.Def_QPBT_QPBT_Games_DistributionAux
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Support
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_linePointDist_nondegenerate_weighted_collision_le

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# Product-distribution weighted collision bounds

This module lifts the nondegenerate weighted collision estimate for one
line-point sample to two independent samples. The nonnegative weight may
depend on the complete second sample and on the first sampled line.

## References

This is formalization-only conditioning support for `lem:qld-xz-lines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:950-955`, using
the collision hypothesis of `lem:pasting` at
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`.
-/



open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

theorem solution
    {L : _root_.MIPStarRE.QPBT.LdParams} {bound : ℕ}
    (weight : _root_.MIPStarRE.QPBT.LineDesc L → (_root_.MIPStarRE.QPBT.LineDesc L × (Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L)) → ℝ)
    (hweight : ∀ line sample, 0 ≤ weight line sample)
    (first second : _root_.MIPStarRE.QPBT.DegPoly L bound) (hne : first ≠ second) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.linePointDist L) (_root_.MIPStarRE.QPBT.linePointDist L)) (fun samples =>
      if samples.1.1.direction ≠ 0 then weight samples.1.1 samples.2 *
        (if _root_.MIPStarRE.QPBT.evalOpt samples.1.1 samples.1.2 first =
          _root_.MIPStarRE.QPBT.evalOpt samples.1.1 samples.1.2 second then 1 else 0) else 0) ≤
    (bound : ℝ) / Fintype.card (_root_.MIPStarRE.QPBT.ScalarQ L) *
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.linePointDist L) (_root_.MIPStarRE.QPBT.linePointDist L)) (fun samples =>
        if samples.1.1.direction ≠ 0 then weight samples.1.1 samples.2 else 0) := by
  classical
  simp only [_root_.MIPStarRE.QPBT.SandwichProduct.avgOver_distribution_prod]
  rw [_root_.LIDT.MIPStarRE.LDT.avgOver_comm, _root_.LIDT.MIPStarRE.LDT.avgOver_comm (_root_.MIPStarRE.QPBT.linePointDist L) (_root_.MIPStarRE.QPBT.linePointDist L)
    (fun firstSample secondSample =>
      if firstSample.1.direction ≠ 0 then weight firstSample.1 secondSample else 0)]
  rw [← _root_.LIDT.MIPStarRE.LDT.avgOver_const_mul]
  apply _root_.LIDT.MIPStarRE.LDT.avgOver_mono
  intro sample
  exact _root_.MIPStarRE.QPBT.linePointDist_nondegenerate_weighted_collision_le
    (fun line => weight line sample) (fun line => hweight line sample)
    first second hne
