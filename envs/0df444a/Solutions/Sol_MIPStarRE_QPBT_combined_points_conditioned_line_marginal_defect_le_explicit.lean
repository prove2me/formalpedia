-- Prove2me | solution 1 for MIPStarRE.QPBT.combined_points_conditioned_line_marginal_defect_le_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T03:27:39.834302+00:00
-- url     : https://prove2.me/submissions/e246f110-71ed-4845-a340-b91e30016f2a

-- Generated proof for MIPStarRE.QPBT.combined_points_conditioned_line_marginal_defect_le_explicit.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Combining_Lines_NondegeneratePastingDistribution
import Definitions.Def_QPBT_QPBT_Combining_Lines_NondegeneratePastingMass
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistributionAux
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Observables_LineMeasurement
import Definitions.Def_QPBT_QPBT_Observables_LineMeasurement_Expanded
import Definitions.Def_QPBT_QPBT_Observables_PointConsistency
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_Setup
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_LIDT_MIPStarRE_Quantum_Measurement_postprocess_comp
import Theorems.Thm_MIPStarRE_QPBT_combined_points_line_marginal_defect_le_explicit
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_integrand_nonneg

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus

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

/-- Conditioning a nonnegative finite average inflates its bound by at most
the inverse retained mass. This is a formalization-only finite probability
estimate used in the conditioning step of `lem:qld-xz-lines`, paper
`14_analysis_of_the_pauli_basis_test.tex:950-963`. -/
theorem avgOver_restrict_le_div_mass {Sample : Type*} [DecidableEq Sample]
    (dist : _root_.LIDT.MIPStarRE.LDT.Distribution Sample) (good : Sample -> Prop) [DecidablePred good]
    (hpos : 0 < ∑ sample ∈ dist.support.filter good, dist.weight sample)
    (value : Sample -> ℝ) (hnonneg : ∀ sample, 0 ≤ value sample) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.Distribution.restrict dist good hpos) value ≤
      _root_.LIDT.MIPStarRE.LDT.avgOver dist value /
        (∑ sample ∈ dist.support.filter good, dist.weight sample) := by
  apply (le_div_iff₀ hpos).mpr
  rw [mul_comm, _root_.MIPStarRE.QPBT.avgOver_restrict_mul_mass]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun sample _ _ => mul_nonneg (dist.nonnegative sample) (hnonneg sample))



end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/Lines/Conditioning.lean. -/
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

@[expose] public section

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open scoped BigOperators Matrix MatrixOrder ComplexOrder

noncomputable section

/-- For arbitrary complete measurements on opposite placements, conditioning
and question relabeling inflate the defect by at most the inverse retained mass.
The needed nonnegativity follows from positivity on opposite registers, not a
new input. Formalization-only support for `eq:pasting-q1`, paper lines 936--963. -/
theorem consistencyDefect_nondegenerateLinePastingDist_le {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (p1 p2 : _root_.MIPStarRE.QPBT.Placement) (hopp : p1.IsOpposite p2)
    (first : ((_root_.MIPStarRE.QPBT.LineDesc P.toLdParams × (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)) ×
      (_root_.MIPStarRE.QPBT.LineDesc P.toLdParams × (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))) →
      _root_.LIDT.MIPStarRE.Quantum.Measurement Outcome (S.ExpandedLocalSpace p1.side))
    (second : ((_root_.MIPStarRE.QPBT.LineDesc P.toLdParams × (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)) ×
      (_root_.MIPStarRE.QPBT.LineDesc P.toLdParams × (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))) →
      _root_.LIDT.MIPStarRE.Quantum.Measurement Outcome (S.ExpandedLocalSpace p2.side)) :
    _root_.MIPStarRE.QPBT.consistencyDefect (_root_.MIPStarRE.QPBT.nondegenerateLinePastingDist P.toLdParams)
      (fun question answer => S.place p1 ((first (question.2, question.1.2)).effect answer))
      (fun question answer => S.place p2 ((second (question.2, question.1.2)).effect answer))
      S.psiHat ≤
    _root_.MIPStarRE.QPBT.consistencyDefect (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams)
      (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams))
      (fun sample answer => S.place p1 ((first sample).effect answer))
      (fun sample answer => S.place p2 ((second sample).effect answer)) S.psiHat /
      _root_.MIPStarRE.QPBT.nondegenerateLinePastingMass P.toLdParams := by
  unfold _root_.MIPStarRE.QPBT.consistencyDefect _root_.MIPStarRE.QPBT.nondegenerateLinePastingDist
  rw [_root_.LIDT.MIPStarRE.LDT.Distribution.avgOver_map]
  exact _root_.MIPStarRE.QPBT.avgOver_restrict_le_div_mass _ _ _ _ (fun sample =>
    _root_.MIPStarRE.QPBT.consistencyDefect_integrand_nonneg S p1 p2 hopp (first sample) (second sample))









/-! ## Unequal-dimensional bipartite transport -/

open DistanceCalculus in

end

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

theorem solution
    (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (ε δQ : ℝ) (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    (points : _root_.MIPStarRE.QPBT.CombinedPointsWitness S δQ)
    (p1 p2 : _root_.MIPStarRE.QPBT.Placement) (hopp : p1.IsOpposite p2) :
        _root_.MIPStarRE.QPBT.consistencyDefect (_root_.MIPStarRE.QPBT.nondegenerateLinePastingDist P.toLdParams)
          (fun question answer => S.place p1
            ((((points.Q p1.side question.2.2 question.1.2.2).postprocess
              (fun pair => (some pair.2, some pair.1))).postprocess Prod.fst).effect answer))
          (fun question answer => S.place p2
            ((S.lineEvalMeasExp p2.side .Z question.1.1.2 question.1.2.2).effect answer))
          S.psiHat ≤ (8 * δQ + 2080 * (ε + _root_.MIPStarRE.QPBT.deltaLine ε)) /
            _root_.MIPStarRE.QPBT.nondegenerateLinePastingMass P.toLdParams ∧
        _root_.MIPStarRE.QPBT.consistencyDefect (_root_.MIPStarRE.QPBT.nondegenerateLinePastingDist P.toLdParams)
          (fun question answer => S.place p1
            ((((points.Q p1.side question.2.2 question.1.2.2).postprocess
              (fun pair => (some pair.2, some pair.1))).postprocess Prod.snd).effect answer))
          (fun question answer => S.place p2
            ((S.lineEvalMeasExp p2.side .X question.1.1.1 question.2.2).effect answer))
          S.psiHat ≤ (8 * δQ + 2080 * (ε + _root_.MIPStarRE.QPBT.deltaLine ε)) /
            _root_.MIPStarRE.QPBT.nondegenerateLinePastingMass P.toLdParams := by
  classical
  have hswap (side : _root_.MIPStarRE.QPBT.PlayerSide) (pointX pointZ : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)
      (answer : Option (_root_.MIPStarRE.QPBT.PauliScalar P)) :
      (((points.Q side pointX pointZ).postprocess
        (fun pair => (some pair.2, some pair.1))).postprocess Prod.fst).effect answer =
        (((points.Q side pointX pointZ).postprocess
          (fun pair => (some pair.1, some pair.2))).postprocess Prod.snd).effect answer ∧
      (((points.Q side pointX pointZ).postprocess
        (fun pair => (some pair.2, some pair.1))).postprocess Prod.snd).effect answer =
        (((points.Q side pointX pointZ).postprocess
          (fun pair => (some pair.1, some pair.2))).postprocess Prod.fst).effect answer := by
    simp only [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_comp, and_self]
  simp_rw [(hswap _ _ _ _).1, (hswap _ _ _ _).2]
  have hmass := (_root_.MIPStarRE.QPBT.prod_linePointDist_nondegenerate_mass_pos P.toLdParams).le
  constructor
  · have h := (_root_.MIPStarRE.QPBT.consistencyDefect_nondegenerateLinePastingDist_le S p1 p2 hopp
      (fun sample => ((points.Q p1.side sample.1.2 sample.2.2).postprocess
        (fun pair => (some pair.1, some pair.2))).postprocess Prod.snd)
      (fun sample => S.lineEvalMeasExp p2.side .Z sample.2.1 sample.2.2)).trans
      (div_le_div_of_nonneg_right
        (_root_.MIPStarRE.QPBT.combined_points_line_marginal_defect_le_explicit P ε δQ S points p1 p2 hopp).2
        hmass)
    unfold _root_.MIPStarRE.QPBT.consistencyDefect _root_.MIPStarRE.QPBT.nondegenerateLinePastingDist at h ⊢
    simp only [_root_.LIDT.MIPStarRE.LDT.Distribution.avgOver_map] at h ⊢
    exact h
  · have h := (_root_.MIPStarRE.QPBT.consistencyDefect_nondegenerateLinePastingDist_le S p1 p2 hopp
      (fun sample => ((points.Q p1.side sample.1.2 sample.2.2).postprocess
        (fun pair => (some pair.1, some pair.2))).postprocess Prod.fst)
      (fun sample => S.lineEvalMeasExp p2.side .X sample.1.1 sample.1.2)).trans
      (div_le_div_of_nonneg_right
        (_root_.MIPStarRE.QPBT.combined_points_line_marginal_defect_le_explicit P ε δQ S points p1 p2 hopp).1
        hmass)
    unfold _root_.MIPStarRE.QPBT.consistencyDefect _root_.MIPStarRE.QPBT.nondegenerateLinePastingDist at h ⊢
    simp only [_root_.LIDT.MIPStarRE.LDT.Distribution.avgOver_map] at h ⊢
    exact h
