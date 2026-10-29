-- Prove2me | solution 1 for MIPStarRE.QPBT.combined_points_line_marginal_distance_le_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T03:09:24.867026+00:00
-- url     : https://prove2.me/submissions/99e4c319-c111-4cab-a54f-92e92e341573

-- Generated proof for MIPStarRE.QPBT.combined_points_line_marginal_distance_le_explicit.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Base
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Games_DistributionAux
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Support
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Observables_LineMeasurement
import Definitions.Def_QPBT_QPBT_Observables_LineMeasurement_Expanded
import Definitions.Def_QPBT_QPBT_Observables_LineMeasurement_LinePointOverlap
import Definitions.Def_QPBT_QPBT_Observables_PointConsistency
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_CombinedPointsWitness_marginal_X_distance_le
import Theorems.Thm_MIPStarRE_QPBT_CombinedPointsWitness_marginal_Z_distance_le
import Theorems.Thm_MIPStarRE_QPBT_aLinePointDist_point_marginal_uniform
import Theorems.Thm_MIPStarRE_QPBT_dLinePointDist_point_marginal_uniform
import Theorems.Thm_MIPStarRE_QPBT_exp_line_point_same_placement_distance_le_explicit
import Theorems.Thm_MIPStarRE_QPBT_opFamilyDistSq_le_of_le_of_le
import Theorems.Thm_MIPStarRE_QPBT_uniformDistribution_prod

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting

/- Source helpers from QPBT/Games/DistanceTheorems/Support.lean. -/
/-!
# Finite-dimensional operator estimates for state-dependent distance

This module contains finite-dimensional operator and finite-sum identities used
by the paper-facing distance theorems. It introduces no new mathematical
assumptions or source-facing statements.

## References

- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-395`
- `references/ldt-paper/preliminaries.tex:649-666`
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.DistanceCalculus

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective

























































































/-- Formalization-only auxiliary lemma for Proposition 4.29: state-dependent
operator-family distance is symmetric. -/
theorem opFamilyDistSq_symm {X α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (A B : X → α → _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (ψ : EuclideanSpace ℂ ι) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq μ A B ψ = _root_.MIPStarRE.QPBT.opFamilyDistSq μ B A ψ := by
  unfold _root_.MIPStarRE.QPBT.opFamilyDistSq
  apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
  intro x
  apply Finset.sum_congr rfl
  intro a _
  simp only [_root_.MIPStarRE.QPBT.applyOperatorToState, map_sub, LinearMap.sub_apply]
  rw [norm_sub_rev]

end MIPStarRE.QPBT.DistanceCalculus

/- Source helpers from QPBT/Observables/LineMeasurement/LinePointOverlap.lean. -/
/-!
# Overlap of expanded line and expanded point measurements

This module computes the diagonal overlap, on the expanded state, between an
expanded line measurement on one placement and the expanded point effects
selected by evaluation at the sampled point on the opposite placement. Each
product of convolution terms factorizes into a strategy overlap and an EPR
overlap; the EPR overlap of a Pauli line projector with a Pauli point projector
vanishes unless the line polynomial evaluates to the point value, and then
equals the EPR overlap of the line projector alone. Summing over the
convolution fibers identifies the expanded overlap with the overlap of the
strategy's evaluation classes and its completed point measurement. This is the
computation displayed in items 2 and 3 of the expanded-line consistency lemma.

The sections on the linearity of the state quadratic form, on register
placements, and on the completed point measurements collect formalization-only
auxiliaries: the source uses these facts without stating them.

## References

Items 2 and 3 of `lem:qld-comm-line-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:534-545`,
blueprint `eq:qld-comm-line-pt-cons`, `eq:qld-comm-line-pt-cons2`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## Linearity of the state quadratic form -/



namespace ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}



/-- A register placement of the zero operator is zero. -/
theorem place_zero (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (p : _root_.MIPStarRE.QPBT.Placement) :
    S.place p (0 : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace p.side)) = 0 := by
  ext i j
  cases p <;> simp [_root_.MIPStarRE.QPBT.ProjectiveSetting.place]

















/-! ## Effects of the completed measurement families -/















/-! ## Factorization of opposite placements with distinct Pauli factors -/













end ProjectiveSetting

/-! ## The overlap identity -/







end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/Lines/PointComparison.lean. -/
/-!
# Point and line marginal comparisons

Projection contraction and the original line-point law give the two marginal
comparisons used by the X-Z-X line construction.
The joint-point marginal estimates are imported through `Points` from
`Points.WitnessMarginals`, which retains the same statements and proofs.

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

/-- The point marginal of the line-point law is uniform. This is the
formalization-only averaging step in `eq:pasting-q1`, paper
`14_analysis_of_the_pauli_basis_test.tex:936-941`, using `lem:alnf` and `lem:dlnf`. -/
theorem avgOver_linePointDist_point (L : _root_.MIPStarRE.QPBT.LdParams)
    (value : (Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L) → ℝ) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.linePointDist L) (fun sample => value sample.2) =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L)) value := by
  rw [_root_.MIPStarRE.QPBT.linePointDist, _root_.MIPStarRE.QPBT.avgOver_mix]
  rw [← _root_.LIDT.MIPStarRE.LDT.Distribution.avgOver_map (_root_.MIPStarRE.QPBT.aLinePointDist L) Prod.snd value,
    ← _root_.LIDT.MIPStarRE.LDT.Distribution.avgOver_map (_root_.MIPStarRE.QPBT.dLinePointDist L) Prod.snd value,
    (_root_.MIPStarRE.QPBT.aLinePointDist_point_marginal_uniform L).1,
    (_root_.MIPStarRE.QPBT.dLinePointDist_point_marginal_uniform L).1]
  ring

/-- Independent line-point samples have independent uniform point marginals.
This formalization-only identity transports the point estimates in
`eq:pasting-q1`, paper `14_analysis_of_the_pauli_basis_test.tex:936-941`. -/
theorem avgOver_prod_linePointDist_points (L : _root_.MIPStarRE.QPBT.LdParams)
    (value : (Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L) × (Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L) → ℝ) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.linePointDist L) (_root_.MIPStarRE.QPBT.linePointDist L))
      (fun sample => value (sample.1.2, sample.2.2)) =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution
        ((Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L) × (Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L))) value := by
  rw [_root_.MIPStarRE.QPBT.uniformDistribution_prod, _root_.MIPStarRE.QPBT.SandwichProduct.avgOver_distribution_prod,
    _root_.MIPStarRE.QPBT.SandwichProduct.avgOver_distribution_prod]
  conv_lhs =>
    arg 2
    ext sample
    rw [_root_.MIPStarRE.QPBT.avgOver_linePointDist_point L (fun point => value (sample.2, point))]
  exact _root_.MIPStarRE.QPBT.avgOver_linePointDist_point L
    (fun point => _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution _) (fun other => value (point, other)))

/-- The first postprocessed joint-point effect is its X marginal sum.
This is the definition preceding `eq:qld-qxz-close-to-point`, paper
`14_analysis_of_the_pauli_basis_test.tex:914-926`, not a witness assumption. -/
theorem CombinedPointsWitness.postprocess_fst_effect
    {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε δQ : ℝ} {S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε}
    (points : _root_.MIPStarRE.QPBT.CombinedPointsWitness S δQ) (side : _root_.MIPStarRE.QPBT.PlayerSide)
    (x z : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) (a : _root_.MIPStarRE.QPBT.PauliScalar P) :
    ((points.Q side x z).postprocess Prod.fst).effect a =
      ∑ b, (points.Q side x z).effect (a, b) := by
  classical
  change (∑ pair ∈ Finset.univ.filter (fun pair => pair.1 = a),
    (points.Q side x z).effect pair) = _
  simp only [Finset.sum_filter, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp

/-- The second postprocessed joint-point effect is its Z marginal sum.
Source: `eq:qld-qxz-close-to-point-2`, paper
`14_analysis_of_the_pauli_basis_test.tex:928-930`. -/
theorem CombinedPointsWitness.postprocess_snd_effect
    {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε δQ : ℝ} {S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε}
    (points : _root_.MIPStarRE.QPBT.CombinedPointsWitness S δQ) (side : _root_.MIPStarRE.QPBT.PlayerSide)
    (x z : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) (b : _root_.MIPStarRE.QPBT.PauliScalar P) :
    ((points.Q side x z).postprocess Prod.snd).effect b =
      ∑ a, (points.Q side x z).effect (a, b) := by
  classical
  change (∑ pair ∈ Finset.univ.filter (fun pair => pair.2 = b),
    (points.Q side x z).effect pair) = _
  simp [Finset.sum_filter, Fintype.sum_prod_type]

/-- X marginal distance on the product line-point law, retaining the supplied
point error. This is the first transport step of `eq:pasting-q1`, paper
`14_analysis_of_the_pauli_basis_test.tex:936-941`; no line comparison is assumed. -/
theorem CombinedPointsWitness.marginal_X_linePoint_distance_le
    {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε δQ : ℝ} {S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε}
    (points : _root_.MIPStarRE.QPBT.CombinedPointsWitness S δQ)
    (p1 p2 : _root_.MIPStarRE.QPBT.Placement) (hopp : p1.IsOpposite p2) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams)
      (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams))
      (fun sample a => S.place p1
        (((points.Q p1.side sample.1.2 sample.2.2).postprocess Prod.fst).effect a))
      (fun sample a => S.place p2 ((S.pointMeasExp p2.side .X sample.1.2).effect a))
      S.psiHat ≤ 4 * δQ := by
  classical
  simp_rw [points.postprocess_fst_effect, S.place_finset_sum]
  unfold _root_.MIPStarRE.QPBT.opFamilyDistSq
  rw [_root_.MIPStarRE.QPBT.avgOver_prod_linePointDist_points P.toLdParams (fun xz =>
    ∑ a, ‖_root_.MIPStarRE.QPBT.applyOperatorToState
      ((∑ b, S.place p1 ((points.Q p1.side xz.1 xz.2).effect (a, b))) -
        S.place p2 ((S.pointMeasExp p2.side .X xz.1).effect a)) S.psiHat‖ ^ 2)]
  exact points.marginal_X_distance_le p1 p2 hopp

/-- Z marginal distance on the product line-point law, with the same error as
the uniform-point estimate. Source: `eq:pasting-q1`, paper
`14_analysis_of_the_pauli_basis_test.tex:936-941`. -/
theorem CombinedPointsWitness.marginal_Z_linePoint_distance_le
    {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε δQ : ℝ} {S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε}
    (points : _root_.MIPStarRE.QPBT.CombinedPointsWitness S δQ)
    (p1 p2 : _root_.MIPStarRE.QPBT.Placement) (hopp : p1.IsOpposite p2) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams)
      (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams))
      (fun sample b => S.place p1
        (((points.Q p1.side sample.1.2 sample.2.2).postprocess Prod.snd).effect b))
      (fun sample b => S.place p2 ((S.pointMeasExp p2.side .Z sample.2.2).effect b))
      S.psiHat ≤ 4 * δQ := by
  classical
  simp_rw [points.postprocess_snd_effect, S.place_finset_sum]
  unfold _root_.MIPStarRE.QPBT.opFamilyDistSq
  rw [_root_.MIPStarRE.QPBT.avgOver_prod_linePointDist_points P.toLdParams (fun xz =>
    ∑ b, ‖_root_.MIPStarRE.QPBT.applyOperatorToState
      ((∑ a, S.place p1 ((points.Q p1.side xz.1 xz.2).effect (a, b))) -
        S.place p2 ((S.pointMeasExp p2.side .Z xz.2).effect b)) S.psiHat‖ ^ 2)]
  exact points.marginal_Z_distance_le p1 p2 hopp

/-- Completing both answer alphabets with a zero outcome preserves placed
squared distance. This formalization-only identity reconciles `eq:pasting-q1`
with the completed evaluation convention of `lem:qld-comm-line-cons`. -/
theorem ProjectiveSetting.opFamilyDistSq_postprocess_some
    {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ} (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    {Sample Answer : Type*} [Fintype Answer] [DecidableEq Answer]
    (law : _root_.LIDT.MIPStarRE.LDT.Distribution Sample) (p1 p2 : _root_.MIPStarRE.QPBT.Placement)
    (first : Sample → _root_.LIDT.MIPStarRE.Quantum.Measurement Answer (S.ExpandedLocalSpace p1.side))
    (second : Sample → _root_.LIDT.MIPStarRE.Quantum.Measurement Answer (S.ExpandedLocalSpace p2.side)) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq law
      (fun sample answer => S.place p1 (((first sample).postprocess some).effect answer))
      (fun sample answer => S.place p2 (((second sample).postprocess some).effect answer))
      S.psiHat =
    _root_.MIPStarRE.QPBT.opFamilyDistSq law (fun sample answer => S.place p1 ((first sample).effect answer))
      (fun sample answer => S.place p2 ((second sample).effect answer)) S.psiHat := by
  classical
  unfold _root_.MIPStarRE.QPBT.opFamilyDistSq
  congr 1
  funext sample
  rw [Fintype.sum_option]
  simp [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess,
    _root_.LIDT.MIPStarRE.Quantum.Submeasurement.postprocess, Finset.sum_filter,
    S.place_zero, _root_.MIPStarRE.QPBT.applyOperatorToState]

/-- The completed X marginal has the same `4 * δQ` bound on line-point
samples. Source: the first comparison of `eq:pasting-q1`, paper
`14_analysis_of_the_pauli_basis_test.tex:936-941`, before inserting the line. -/
theorem CombinedPointsWitness.marginal_X_option_linePoint_distance_le
    {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε δQ : ℝ} {S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε}
    (points : _root_.MIPStarRE.QPBT.CombinedPointsWitness S δQ)
    (p1 p2 : _root_.MIPStarRE.QPBT.Placement) (hopp : p1.IsOpposite p2) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams)
      (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams))
      (fun sample answer => S.place p1
        ((((points.Q p1.side sample.1.2 sample.2.2).postprocess Prod.fst).postprocess
          some).effect answer))
      (fun sample answer => S.place p2
        ((S.pointMeasExpOption p2.side .X sample.1.2).effect answer))
      S.psiHat ≤ 4 * δQ := by
  unfold _root_.MIPStarRE.QPBT.ProjectiveSetting.pointMeasExpOption
  erw [S.opFamilyDistSq_postprocess_some]
  exact points.marginal_X_linePoint_distance_le p1 p2 hopp

/-- The completed Z marginal has the same `4 * δQ` bound on line-point
samples. Source: the second comparison of `eq:pasting-q1`, paper
`14_analysis_of_the_pauli_basis_test.tex:936-941`, before inserting the line. -/
theorem CombinedPointsWitness.marginal_Z_option_linePoint_distance_le
    {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε δQ : ℝ} {S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε}
    (points : _root_.MIPStarRE.QPBT.CombinedPointsWitness S δQ)
    (p1 p2 : _root_.MIPStarRE.QPBT.Placement) (hopp : p1.IsOpposite p2) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams)
      (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams))
      (fun sample answer => S.place p1
        ((((points.Q p1.side sample.1.2 sample.2.2).postprocess Prod.snd).postprocess
          some).effect answer))
      (fun sample answer => S.place p2
        ((S.pointMeasExpOption p2.side .Z sample.2.2).effect answer))
      S.psiHat ≤ 4 * δQ := by
  unfold _root_.MIPStarRE.QPBT.ProjectiveSetting.pointMeasExpOption
  erw [S.opFamilyDistSq_postprocess_some]
  exact points.marginal_Z_linePoint_distance_le p1 p2 hopp























end

end MIPStarRE.QPBT

/-!
# Point and line marginal comparisons

Projection contraction and the original line-point law give the two marginal
comparisons used by the X-Z-X line construction.
The joint-point marginal estimates are imported through `Points` from
`Points.WitnessMarginals`, which retains the same statements and proofs.

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
        _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams)
          (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams))
          (fun sample answer => S.place p1
            ((((points.Q p1.side sample.1.2 sample.2.2).postprocess Prod.fst).postprocess
              some).effect answer))
          (fun sample answer => S.place p2
            ((S.lineEvalMeasExp p2.side .X sample.1.1 sample.1.2).effect answer))
          S.psiHat ≤ 8 * δQ + 2080 * (ε + _root_.MIPStarRE.QPBT.deltaLine ε) ∧
        _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams)
          (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams))
          (fun sample answer => S.place p1
            ((((points.Q p1.side sample.1.2 sample.2.2).postprocess Prod.snd).postprocess
              some).effect answer))
          (fun sample answer => S.place p2
            ((S.lineEvalMeasExp p2.side .Z sample.2.1 sample.2.2).effect answer))
          S.psiHat ≤ 8 * δQ + 2080 * (ε + _root_.MIPStarRE.QPBT.deltaLine ε) := by
  classical
  have hX : _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams)
      (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams))
      (fun sample answer => S.place p2
        ((S.pointMeasExpOption p2.side .X sample.1.2).effect answer))
      (fun sample answer => S.place p2
        ((S.lineEvalMeasExp p2.side .X sample.1.1 sample.1.2).effect answer))
      S.psiHat ≤ 1040 * (ε + _root_.MIPStarRE.QPBT.deltaLine ε) := by
    rw [_root_.MIPStarRE.QPBT.DistanceCalculus.opFamilyDistSq_symm]
    unfold _root_.MIPStarRE.QPBT.opFamilyDistSq
    rw [_root_.MIPStarRE.QPBT.SandwichProduct.avgOver_distribution_prod]
    simp_rw [_root_.LIDT.MIPStarRE.LDT.avgOver_const_of_isProbability _ (_root_.MIPStarRE.QPBT.linePointDist_isProbability P.toLdParams)]
    exact _root_.MIPStarRE.QPBT.exp_line_point_same_placement_distance_le_explicit P ε S p1 p2 hopp .X
  have hZ : _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams)
      (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams))
      (fun sample answer => S.place p2
        ((S.pointMeasExpOption p2.side .Z sample.2.2).effect answer))
      (fun sample answer => S.place p2
        ((S.lineEvalMeasExp p2.side .Z sample.2.1 sample.2.2).effect answer))
      S.psiHat ≤ 1040 * (ε + _root_.MIPStarRE.QPBT.deltaLine ε) := by
    rw [_root_.MIPStarRE.QPBT.DistanceCalculus.opFamilyDistSq_symm]
    unfold _root_.MIPStarRE.QPBT.opFamilyDistSq
    rw [_root_.MIPStarRE.QPBT.SandwichProduct.avgOver_distribution_prod]
    erw [_root_.LIDT.MIPStarRE.LDT.avgOver_const_of_isProbability _ (_root_.MIPStarRE.QPBT.linePointDist_isProbability P.toLdParams)
      (_root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams)
        (fun sample answer => S.place p2
          ((S.lineEvalMeasExp p2.side .Z sample.1 sample.2).effect answer))
        (fun sample answer => S.place p2
          ((S.pointMeasExpOption p2.side .Z sample.2).effect answer)) S.psiHat)]
    exact _root_.MIPStarRE.QPBT.exp_line_point_same_placement_distance_le_explicit P ε S p1 p2 hopp .Z
  constructor
  · convert _root_.MIPStarRE.QPBT.opFamilyDistSq_le_of_le_of_le _ _ _ _ S.psiHat _ _
      (points.marginal_X_option_linePoint_distance_le p1 p2 hopp) hX using 1
    ring
  · convert _root_.MIPStarRE.QPBT.opFamilyDistSq_le_of_le_of_le _ _ _ _ S.psiHat _ _
      (points.marginal_Z_option_linePoint_distance_le p1 p2 hopp) hZ using 1
    ring
