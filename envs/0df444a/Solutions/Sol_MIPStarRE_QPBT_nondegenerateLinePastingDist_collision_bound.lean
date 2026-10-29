-- Prove2me | solution 1 for MIPStarRE.QPBT.nondegenerateLinePastingDist_collision_bound
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:42:39.550224+00:00
-- url     : https://prove2.me/submissions/f83b2c2c-9238-430a-ac23-ca0cec4bd2e5

-- Generated proof for MIPStarRE.QPBT.nondegenerateLinePastingDist_collision_bound.
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
import Definitions.Def_QPBT_QPBT_Combining_Lines_NondegeneratePastingDistribution
import Definitions.Def_QPBT_QPBT_Games_DistributionAux
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Defs
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_Setup
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_collision_bound_of_fiber_averages
import Theorems.Thm_MIPStarRE_QPBT_prod_linePointDist_nondegenerate_weighted_collision_le

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Games/RestrictedAverage.lean. -/
/-!
# Averages over restricted finite distributions

This module records a generic comparison between a nonnegative average and
the corresponding average after conditioning on a positive-mass event.

## References

The estimate supports the proof-only conditioning step in `lem:qld-xz-lines`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:950-963`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

/-- Multiplying a normalized restricted average by its retained mass gives the
unnormalized restricted sum. This formalization-only identity supports
proof-only conditioning in `lem:qld-xz-lines`, paper
`14_analysis_of_the_pauli_basis_test.tex:950-963`; it changes no game distribution. -/
theorem avgOver_restrict_mul_mass {Sample : Type*} [DecidableEq Sample]
    (dist : _root_.LIDT.MIPStarRE.LDT.Distribution Sample) (good : Sample -> Prop) [DecidablePred good]
    (hpos : 0 < ∑ sample ∈ dist.support.filter good, dist.weight sample)
    (value : Sample -> ℝ) :
    (∑ sample ∈ dist.support.filter good, dist.weight sample) *
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.Distribution.restrict dist good hpos) value =
      ∑ sample ∈ dist.support.filter good, dist.weight sample * value sample := by
  unfold _root_.LIDT.MIPStarRE.LDT.avgOver _root_.MIPStarRE.QPBT.Distribution.restrict
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro sample hsample
  simp only [if_pos (Finset.mem_filter.mp hsample).2]
  field_simp





end MIPStarRE.QPBT

/-!
# Conditional collision bound for nondegenerate line pasting

This module verifies the conditional collision hypothesis used when applying
the pasting lemma to the proof-only nondegenerate line-pasting distribution.

## References

The collision estimate supports `lem:qld-xz-lines` at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:950-963` and
instantiates the hypothesis of `lem:pasting` at
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`.
-/



open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

theorem solution
    (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (bound : ℕ) :
    _root_.MIPStarRE.QPBT.HasConditionalCollisionBound (_root_.MIPStarRE.QPBT.nondegenerateLinePastingDist P.toLdParams)
      (fun (poly : _root_.MIPStarRE.QPBT.DegPoly P.toLdParams bound) sample => _root_.MIPStarRE.QPBT.evalOpt sample.1 sample.2 poly)
      ((bound : ℝ) / Fintype.card (_root_.MIPStarRE.QPBT.ScalarQ P.toLdParams)) := by
  classical
  apply _root_.MIPStarRE.QPBT.collision_bound_of_fiber_averages
  intro fixed first second hne
  simp only [_root_.MIPStarRE.QPBT.nondegenerateLinePastingDist, _root_.LIDT.MIPStarRE.LDT.Distribution.avgOver_map]
  have hpos := _root_.MIPStarRE.QPBT.prod_linePointDist_nondegenerate_mass_pos P.toLdParams
  apply (mul_le_mul_iff_right₀ hpos).mp
  rw [_root_.MIPStarRE.QPBT.avgOver_restrict_mul_mass, mul_left_comm _ ((bound : ℝ) /
    Fintype.card (_root_.MIPStarRE.QPBT.ScalarQ P.toLdParams)), _root_.MIPStarRE.QPBT.avgOver_restrict_mul_mass]
  have h := _root_.MIPStarRE.QPBT.prod_linePointDist_nondegenerate_weighted_collision_le
    (fun line sample => if ((line, sample.1), sample) = fixed then 1 else 0)
    (fun line sample => by split_ifs <;> norm_num) first second hne
  have hswap (condition other : Prop) [Decidable condition] [Decidable other] (value : ℝ) :
      (if condition then (if other then value else 0) else 0) =
        (if other then (if condition then value else 0) else 0) := by
    split_ifs <;> rfl
  rw [Finset.sum_filter, Finset.sum_filter]
  unfold _root_.LIDT.MIPStarRE.LDT.avgOver at h
  simp only [mul_ite, mul_one, mul_zero] at h ⊢
  convert h using 1
  · rfl
  · apply Finset.sum_congr rfl
    intro sample _
    split_ifs <;> rfl
