-- Prove2me | solution 1 for MIPStarRE.QPBT.subline_joint_overlap_near_one_at_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:37:43.275978+00:00
-- url     : https://prove2.me/submissions/538936e6-0100-4f54-81e4-12ec6b1a98a3

-- Generated proof for MIPStarRE.QPBT.subline_joint_overlap_near_one_at_explicit.
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
import Definitions.Def_QPBT_QPBT_Combining_Defs
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLines_Overlap
import Definitions.Def_QPBT_QPBT_Combining_SubLineZDeficit
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Observables_LineMeasurement_Expanded
import Definitions.Def_QPBT_QPBT_Observables_PointConsistency
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_SubLineWitness_paired_ordered_overlap_gap_le
import Theorems.Thm_MIPStarRE_QPBT_subline_remove_x_factor_at_explicit
import Theorems.Thm_MIPStarRE_QPBT_subline_z_term_near_one_at_explicit

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting

/- Source helpers from QPBT/Combining/ErrorBounds.lean. -/
/-! # Scalar error bounds for combining polynomial measurements

This module proves the formalization-only scalar estimates used by the combining
argument: nonnegativity of the real fourth root, the quarter-power form of a
square root of two deficit terms, polynomial bounds after conditioning,
composition with the dimension factor retained, and absorption into the global
polynomial-pair error scale. The estimates quantify over error functions and
numerical parameters; they do not construct measurements, and none of them is
specific to Claims 17-1 through 17-3.

## References

The auxiliary blueprint statements are `thm:qld-conditioned-polynomial-bound`,
`thm:qld-combining-polynomial-bound`, and `thm:qld-global-pair-error-bound` in
`blueprint/src/chapter/ch15_qpbt_combining.tex`. They support the calculations
in `lem:qld-xz-lines`, `lem:qld-4-13`, and `lem:qld-4-7` of
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:950-963,1134-1246`
and `:1278-1288,1402`. The corrected error notation and the retained dimension
factor are documented in `docs/paper-gaps/qpbt_combined-lines-error-term.tex`.
-/

@[expose] public section

namespace MIPStarRE.QPBT

/-- The real fourth root is nonnegative on all of `ℝ`. For `x < 0` the real power
`x ^ (1/4)` is defined as `|x| ^ (1/4) * cos (π/4)`, which is positive, and for
`0 ≤ x` it is the usual fourth root. The estimates of `lem:qld-4-13` are stated
with quarter powers of error quantities whose nonnegativity is not always
available at the point of use, so the bound is recorded without a sign
hypothesis. -/
theorem rpow_quarter_nonneg (x : ℝ) : 0 ≤ Real.rpow x (1 / 4 : ℝ) := by
  change 0 ≤ x ^ (1 / 4 : ℝ)
  rcases lt_or_ge x 0 with hx | hx
  · rw [Real.rpow_def_of_neg hx,
      show (1 / 4 : ℝ) * Real.pi = Real.pi / 4 by ring, Real.cos_pi_div_four]
    positivity
  · exact Real.rpow_nonneg hx _















end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/ExtendedLines/Estimates.lean. -/
/-!
# Estimates for the extended-line construction

This construction uses the directly indexed extended-line space, the answer
alphabet obtained from the field by adjoining an undefined-evaluation outcome,
and the corrected sum-form convention for polynomial errors.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1118-1246`,
blueprint `lem:qld-4-13-established`.
See `docs/paper-gaps/qpbt_combined-lines-error-term.tex` and
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex` for the remaining
comparison with the printed source theorem.
-/

@[expose] public section

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open scoped BigOperators Matrix MatrixOrder ComplexOrder

noncomputable section









/-- Expand the state quadratic form before specializing the register carrier. -/
private theorem stateQForm_eq_inner_mulVec {Carrier : Type*}
    [Fintype Carrier] [DecidableEq Carrier]
    (state : EuclideanSpace ℂ Carrier) (operator : _root_.LIDT.MIPStarRE.Quantum.Op Carrier) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm state operator = (inner ℂ state
      ((EuclideanSpace.equiv Carrier ℂ).symm (operator.mulVec state))).re := rfl






end

end MIPStarRE.QPBT

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





















/-! ## Effects of the completed measurement families -/





/-- The completed expanded point measurement agrees with the expanded point
measurement on proper values. -/
theorem pointMeasExpOption_effect_some (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    (side : _root_.MIPStarRE.QPBT.PlayerSide) (W : _root_.MIPStarRE.QPBT.PauliKind) (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)
    (b : _root_.MIPStarRE.QPBT.PauliScalar P) :
    (S.pointMeasExpOption side W u).effect (some b) =
      (S.pointMeasExp side W u).effect b := by
  unfold _root_.MIPStarRE.QPBT.ProjectiveSetting.pointMeasExpOption
  rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect]
  simp [Finset.filter_eq']

/-- The completed expanded point measurement assigns zero to `none`. -/
theorem pointMeasExpOption_effect_none (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    (side : _root_.MIPStarRE.QPBT.PlayerSide) (W : _root_.MIPStarRE.QPBT.PauliKind) (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) :
    (S.pointMeasExpOption side W u).effect none = 0 := by
  unfold _root_.MIPStarRE.QPBT.ProjectiveSetting.pointMeasExpOption
  rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect]
  apply Finset.sum_eq_zero
  intro a ha
  exact absurd (Finset.mem_filter.mp ha).2 (by simp)

/-- The expanded point effect selected by a line answer is the completed
expanded point effect at the partial evaluation of the answer. This
identifies the two presentations of item 2 and item 3 of
`lem:qld-comm-line-cons`, blueprint `eq:qld-comm-line-pt-cons`, `eq:qld-comm-line-pt-cons2`. -/
theorem pointMeasExpOption_effect_evalOpt (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    (side : _root_.MIPStarRE.QPBT.PlayerSide) (W : _root_.MIPStarRE.QPBT.PauliKind) (line : _root_.MIPStarRE.QPBT.LineDesc P.toLdParams)
    (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) (f : _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d)) :
    (S.pointMeasExpOption side W u).effect (_root_.MIPStarRE.QPBT.evalOpt line u f) =
      S.expPointEffectAtLineAnswer side W line u f := by
  unfold _root_.MIPStarRE.QPBT.ProjectiveSetting.expPointEffectAtLineAnswer
  cases _root_.MIPStarRE.QPBT.evalOpt line u f with
  | none => exact S.pointMeasExpOption_effect_none side W u
  | some a => exact S.pointMeasExpOption_effect_some side W u a





/-! ## Factorization of opposite placements with distinct Pauli factors -/













end ProjectiveSetting

/-! ## The overlap identity -/







end

end MIPStarRE.QPBT

/-!
# Estimates for the extended-line construction

This construction uses the directly indexed extended-line space, the answer
alphabet obtained from the field by adjoining an undefined-evaluation outcome,
and the corrected sum-form convention for polynomial errors.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1118-1246`,
blueprint `lem:qld-4-13-established`.
See `docs/paper-gaps/qpbt_combined-lines-error-term.tex` and
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex` for the remaining
comparison with the printed source theorem.
-/



open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open scoped BigOperators Matrix MatrixOrder ComplexOrder

set_option maxHeartbeats 800000 in
-- Expanding the nested averages and matrix quadratic forms is elaboration-intensive.

theorem solution
    (params : _root_.MIPStarRE.QPBT.AdmissibleParams) (error pointError lineError : ℝ)
    (setting : _root_.MIPStarRE.QPBT.ProjectiveSetting params error)
    (points : _root_.MIPStarRE.QPBT.CombinedPointsWitness setting pointError)
    (lines : _root_.MIPStarRE.QPBT.CombinedLinesWitness setting points lineError) (sublines : _root_.MIPStarRE.QPBT.SubLineWitness params)
    (first second : _root_.MIPStarRE.QPBT.Placement) (hopposite : first.IsOpposite second) :
    |avgOver sublines.D (_root_.MIPStarRE.QPBT.pairedSublineOverlap setting points lines first second) - 1| ≤
      6 * (pointError ^ (1 / 2 : ℝ) + Real.sqrt (params.m : ℝ) *
        (lineError ^ (1 / 4 : ℝ) + pointError ^ (1 / 4 : ℝ) +
          error ^ (1 / 4 : ℝ))) := by
  let zOverlap := _root_.LIDT.MIPStarRE.LDT.avgOver sublines.D (fun sample =>
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectScalarQ params.extendedDirectLd)) (fun parameter =>
      _root_.MIPStarRE.QPBT.zPointOverlapAt lines first second (sample.2, _root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli params
        (sample.1.base + parameter • sample.1.direction)))))
  have hfirst : |avgOver sublines.D
      (_root_.MIPStarRE.QPBT.pairedSublineOverlap setting points lines first second) - _root_.LIDT.MIPStarRE.LDT.avgOver sublines.D
        (_root_.MIPStarRE.QPBT.orderedSublineOverlap setting points lines first second)| ≤
      2 * pointError ^ (1 / 2 : ℝ) := by
    have heq : Real.sqrt (4 * pointError) = 2 * pointError ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num [Real.sqrt_eq_rpow]
    exact (sublines.paired_ordered_overlap_gap_le lines first second).trans_eq heq
  have hsecond : |avgOver sublines.D
      (_root_.MIPStarRE.QPBT.orderedSublineOverlap setting points lines first second) - zOverlap| ≤
      2 * Real.sqrt (params.m : ℝ) *
        (lineError ^ (1 / 4 : ℝ) + pointError ^ (1 / 4 : ℝ)) := by
    have hbound := _root_.MIPStarRE.QPBT.subline_remove_x_factor_at_explicit params error pointError lineError
      setting points lines sublines first second hopposite
    simp only [← _root_.MIPStarRE.QPBT.ProjectiveSetting.pointMeasExpOption_effect_evalOpt] at hbound
    unfold _root_.MIPStarRE.QPBT.orderedSublineOverlap zOverlap _root_.MIPStarRE.QPBT.zPointOverlapAt
    simp only [Fintype.sum_prod_type, stateQForm_eq_inner_mulVec]
    with_unfolding_all exact hbound
  have hthird : |zOverlap - 1| ≤ 2 * Real.sqrt (params.m : ℝ) *
      (lineError ^ (1 / 4 : ℝ) + pointError ^ (1 / 4 : ℝ) + error ^ (1 / 4 : ℝ)) := by
    have hbound := _root_.MIPStarRE.QPBT.subline_z_term_near_one_at_explicit params error pointError lineError
      setting points lines sublines first second hopposite
    simp only [← _root_.MIPStarRE.QPBT.ProjectiveSetting.pointMeasExpOption_effect_evalOpt] at hbound
    unfold zOverlap _root_.MIPStarRE.QPBT.zPointOverlapAt
    simp only [stateQForm_eq_inner_mulVec]
    with_unfolding_all exact hbound
  have hchain := (abs_sub_le _ _ (1 : ℝ)).trans
    (add_le_add hfirst ((abs_sub_le _ zOverlap (1 : ℝ)).trans (add_le_add hsecond hthird)))
  have hhalf : 0 ≤ pointError ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_nonneg _
  have hsum : 0 ≤ lineError ^ (1 / 4 : ℝ) + pointError ^ (1 / 4 : ℝ) :=
    add_nonneg (_root_.MIPStarRE.QPBT.rpow_quarter_nonneg _) (_root_.MIPStarRE.QPBT.rpow_quarter_nonneg _)
  have hquarter := _root_.MIPStarRE.QPBT.rpow_quarter_nonneg error
  simp only [Real.rpow_eq_pow] at hquarter
  have hdimension := Real.sqrt_nonneg (params.m : ℝ)
  refine hchain.trans ?_
  nlinarith [mul_nonneg hdimension hsum, mul_nonneg hdimension hquarter]
