-- Prove2me | solution 1 for MIPStarRE.QPBT.consistencyDefect_le_nondegenerateLinePastingDist_add_mass
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:02:01.93864+00:00
-- url     : https://prove2.me/submissions/9fef71c6-c4e7-42a7-8d2e-6f9ca9bf402d

-- Generated proof for MIPStarRE.QPBT.consistencyDefect_le_nondegenerateLinePastingDist_add_mass.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Combining_Lines_NondegeneratePastingDistribution
import Definitions.Def_QPBT_QPBT_Combining_Lines_NondegeneratePastingMass
import Definitions.Def_QPBT_QPBT_Combining_Lines_ZeroDirectionMass
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistributionAux
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Support
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Observables_PointConsistency
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_Setup
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_integrand_le_one
import Theorems.Thm_MIPStarRE_QPBT_dLinePointDist_zero_direction_mass_le

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus

/- Source helpers from QPBT/Combining/Lines/DiscardedMass.lean. -/
/-! # Discarded zero-direction mass

## References

Paper `lem:qld-xz-lines`, lines 950--963.
-/

@[expose] public section

namespace MIPStarRE.QPBT
open LIDT.MIPStarRE.LDT
noncomputable section




/-- The equal mixture of axis and diagonal line-point laws gives zero directions
mass at most `1 / (2q)`. This formalization-only estimate preserves the source sampler of
`def:line-point-dist`, paper `08_classical_and_quantum_low_degree_tests.tex:274-287`,
including its degenerate fibers. -/
theorem linePointDist_zero_direction_mass_le (L : _root_.MIPStarRE.QPBT.LdParams) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.linePointDist L) (fun sample =>
      if sample.1.direction = 0 then 1 else 0) ≤
      1 / (2 * Fintype.card (_root_.MIPStarRE.QPBT.ScalarQ L)) := by
  rw [_root_.MIPStarRE.QPBT.linePointDist, _root_.MIPStarRE.QPBT.avgOver_mix, _root_.MIPStarRE.QPBT.aLinePointDist_zero_direction_mass]
  have hdiag := _root_.MIPStarRE.QPBT.dLinePointDist_zero_direction_mass_le L
  calc
    _ = (1 / 2 : ℝ) * _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.dLinePointDist L)
        (fun sample => if sample.1.direction = 0 then 1 else 0) := by ring
    _ ≤ (1 / 2 : ℝ) * (1 / Fintype.card (_root_.MIPStarRE.QPBT.ScalarQ L)) :=
      mul_le_mul_of_nonneg_left hdiag (by norm_num)
    _ = _ := by rw [one_div_mul_one_div]




/-- For two independent line-point samples, excluding only zero X directions
costs at most `1 / (2q)`. Only X requires the collision estimate when the
X-outer sandwich is instantiated with `G2 = X`. This is a formalization-only bound for
paper `14_analysis_of_the_pauli_basis_test.tex:943-963`. -/
theorem prod_linePointDist_zero_X_direction_mass_le (L : _root_.MIPStarRE.QPBT.LdParams) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.linePointDist L) (_root_.MIPStarRE.QPBT.linePointDist L))
      (fun samples => if samples.1.1.direction = 0 then 1 else 0) ≤
      1 / (2 * Fintype.card (_root_.MIPStarRE.QPBT.ScalarQ L)) := by
  rw [_root_.MIPStarRE.QPBT.SandwichProduct.avgOver_distribution_prod]
  change _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.linePointDist L) (fun sample => _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.linePointDist L)
    (fun _ => if sample.1.direction = 0 then 1 else 0)) ≤ _
  simp_rw [_root_.LIDT.MIPStarRE.LDT.avgOver_const_of_isProbability _ (_root_.MIPStarRE.QPBT.linePointDist_isProbability L)]
  exact _root_.MIPStarRE.QPBT.linePointDist_zero_direction_mass_le L


end
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



/-- An average of a function bounded above by one is at most the retained mass
times its conditional average, plus the discarded probability mass. This
formalization-only estimate restores the original distribution after proof-only
conditioning in `lem:qld-xz-lines`, paper
`14_analysis_of_the_pauli_basis_test.tex:950-963`. No discarded mass is omitted. -/
theorem avgOver_le_restrict_add_discarded_mass {Sample : Type*} [DecidableEq Sample]
    (dist : _root_.LIDT.MIPStarRE.LDT.Distribution Sample) (good : Sample -> Prop) [DecidablePred good]
    (hpos : 0 < ∑ sample ∈ dist.support.filter good, dist.weight sample)
    (value : Sample -> ℝ) (hunit : ∀ sample, value sample ≤ 1) :
    _root_.LIDT.MIPStarRE.LDT.avgOver dist value ≤
      (∑ sample ∈ dist.support.filter good, dist.weight sample) *
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.Distribution.restrict dist good hpos) value +
      ∑ sample ∈ dist.support.filter (fun sample => ¬ good sample), dist.weight sample := by
  classical
  rw [_root_.MIPStarRE.QPBT.avgOver_restrict_mul_mass]
  unfold _root_.LIDT.MIPStarRE.LDT.avgOver
  rw [← Finset.sum_filter_add_sum_filter_not dist.support good
    (fun sample => dist.weight sample * value sample)]
  exact add_le_add_right (Finset.sum_le_sum fun sample _ =>
    mul_le_of_le_one_right (dist.nonnegative sample) (hunit sample)) _

end MIPStarRE.QPBT

/-!
# Conditioning the line-pasting distribution

The proof conditions only on nonzero X directions. Conditional collision
bounds apply there, and the discarded probability is restored explicitly.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:882-963`,
blueprint `lem:qld-xz-lines`. The source and completed-answer distinctions remain
as documented in
`docs/paper-gaps/qpbt_combined-lines-error-term.tex`.
-/



open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open scoped BigOperators Matrix MatrixOrder ComplexOrder

set_option maxHeartbeats 800000 in
-- Transport through the mapped product distribution expands two postprocessed families.

theorem solution
    {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (p1 p2 : _root_.MIPStarRE.QPBT.Placement) (hopp : p1.IsOpposite p2)
    (first : ((_root_.MIPStarRE.QPBT.LineDesc P.toLdParams × (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)) ×
      (_root_.MIPStarRE.QPBT.LineDesc P.toLdParams × (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))) →
      _root_.LIDT.MIPStarRE.Quantum.Measurement Outcome (S.ExpandedLocalSpace p1.side))
    (second : ((_root_.MIPStarRE.QPBT.LineDesc P.toLdParams × (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)) ×
      (_root_.MIPStarRE.QPBT.LineDesc P.toLdParams × (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))) →
      _root_.LIDT.MIPStarRE.Quantum.Measurement Outcome (S.ExpandedLocalSpace p2.side)) :
    _root_.MIPStarRE.QPBT.consistencyDefect (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams)
      (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams))
      (fun sample answer => S.place p1 ((first sample).effect answer))
      (fun sample answer => S.place p2 ((second sample).effect answer)) S.psiHat ≤
    _root_.MIPStarRE.QPBT.nondegenerateLinePastingMass P.toLdParams *
      _root_.MIPStarRE.QPBT.consistencyDefect (_root_.MIPStarRE.QPBT.nondegenerateLinePastingDist P.toLdParams)
        (fun question answer => S.place p1 ((first (question.2, question.1.2)).effect answer))
        (fun question answer => S.place p2 ((second (question.2, question.1.2)).effect answer))
        S.psiHat + 1 / (2 * Fintype.card (_root_.MIPStarRE.QPBT.ScalarQ P.toLdParams)) := by
  classical
  unfold _root_.MIPStarRE.QPBT.consistencyDefect _root_.MIPStarRE.QPBT.nondegenerateLinePastingDist _root_.MIPStarRE.QPBT.nondegenerateLinePastingMass
  rw [_root_.LIDT.MIPStarRE.LDT.Distribution.avgOver_map]
  let value := fun sample => ∑ answer : Outcome, ∑ other : Outcome,
      if answer = other then 0 else (inner ℂ S.psiHat
        ((EuclideanSpace.equiv (_root_.MIPStarRE.QPBT.SixReg P S.toStrategy.ιA S.toStrategy.ιB) ℂ).symm
          ((S.place p1 ((first sample).effect answer) *
            S.place p2 ((second sample).effect other)).mulVec S.psiHat))).re
  have hunit : ∀ sample, value sample ≤ 1 := fun sample =>
    _root_.MIPStarRE.QPBT.consistencyDefect_integrand_le_one S p1 p2 hopp (first sample) (second sample)
  have h := _root_.MIPStarRE.QPBT.avgOver_le_restrict_add_discarded_mass _
    (fun samples => samples.1.1.direction ≠ 0)
    (_root_.MIPStarRE.QPBT.prod_linePointDist_nondegenerate_mass_pos P.toLdParams) value hunit
  have hdiscard : (∑ sample ∈ (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams)
      (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams)).support.filter (fun sample => ¬ sample.1.1.direction ≠ 0),
      (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams)
        (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams)).weight sample) ≤
      1 / (2 * Fintype.card (_root_.MIPStarRE.QPBT.ScalarQ P.toLdParams)) := by
    rw [_root_.MIPStarRE.QPBT.Distribution.sum_filter_weight_eq_avgOver]
    simpa only [ne_eq, not_not] using _root_.MIPStarRE.QPBT.prod_linePointDist_zero_X_direction_mass_le P.toLdParams
  have hfinal := h.trans (add_le_add_right hdiscard _)
  exact hfinal
