-- Prove2me | solution 1 for MIPStarRE.QPBT.SubLineWitness.extendedPointOverlap_ge
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:44:57.523245+00:00
-- url     : https://prove2.me/submissions/fdc3c5b8-94f7-4f58-bc29-eeec97aea0c9

-- Generated proof for MIPStarRE.QPBT.SubLineWitness.extendedPointOverlap_ge.
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
import Definitions.Def_QPBT_QPBT_Combining_Defs
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLines_Measurement
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLines_Overlap
import Definitions.Def_QPBT_QPBT_Combining_Points_PlacementSupport
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Observables_PointConsistency
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_quadratic_form_mono
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_place_comm
import Theorems.Thm_MIPStarRE_QPBT_SubLineWitness_completedPoint_effect_le
import Theorems.Thm_MIPStarRE_QPBT_SubLineWitness_extendedMeasurement_overlap

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

/- Source helpers from QPBT/Combining/Lines/ConsistencyPositivity.lean. -/
/-!
# Positivity of the consistency defect on opposite placements

The error-inflation estimates for restricted line distributions apply to
nonnegative averages.  This module supplies the missing nonnegativity: the
integrand of `consistencyDefect` for two complete measurements placed on
opposite registers is a state quadratic form of a positive operator.  Indeed,
after separating the two placements along the corresponding tensor
bipartition, the off-diagonal sum is
`∑_a (place p₁ E_a) (place p₂ (∑_{b ≠ a} F_b))`, a sum of products of
positive operators supported on complementary registers.  The placement
algebra itself — additivity, the image of zero, positivity and the commutation
of opposite placements — is supplied by the placement identities proved in
`MIPStarRE.QPBT.Combining.Points.PlacementSupport` and
`MIPStarRE.QPBT.Observables.LineMeasurement.LinePointOverlap`.

## References

The consistency defect is blueprint `def:consistency`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:232-248`.  The
placements and their bipartitions are blueprint `def:expanded-state`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:420-450`.  The
nonnegativity is the hypothesis of items 1 and 2 of
blueprint `lem:restricted-line-mixture-bounds`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1052-1058`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}

/-- Positive operators placed on a directed opposite pair of registers have a
positive product.  Paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:420-450`,
blueprint `def:expanded-state`. -/
theorem place_mul_place_nonneg (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    (p₁ p₂ : _root_.MIPStarRE.QPBT.Placement) (hopp : p₁.IsOpposite p₂)
    {X : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace p₁.side)}
    {Y : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace p₂.side)}
    (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    0 ≤ S.place p₁ X * S.place p₂ Y := by
  exact Commute.mul_nonneg (S.place_nonneg p₁ hX) (S.place_nonneg p₂ hY)
    (S.place_comm p₁ p₂ hopp X Y)





end ProjectiveSetting

/-! ## Nonnegativity of the pointwise consistency defect -/





end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Observables/ExpandedPlacement.lean. -/
/-!
# Placing operators on the expanded state

The four register placements of `def:symmetric-equivalents` put an operator of
one player's expanded local space on one of the register pairs `AA'`, `BA''`,
`BB'` and `AB''` of the expanded state `psiHat`.  This module records how such
a placement acts on `psiHat`: after the shuffle of `eq:def-psihat` the placed
operator is a threefold tensor product, so a factorized operator whose Pauli
factor is an isometry has the same state-dependent norm as its strategy factor
placed on the original state.  No symmetry between the two players is used;
each of the four placements is treated explicitly.

## References

The declarations support `def:symmetric-equivalents` and `lem:qld-comm-cons`
in `blueprint/src/chapter/ch14_qpbt_observables.tex:1002-1031` and
`blueprint/src/chapter/ch14_qpbt_observables.tex:1139-1178`.  Their paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:420-505`.
-/

@[expose] public section

-- The unshuffled six-register index type of `eq:def-psihat` is a fourfold
-- iterated product; instance search for its `Fintype` and `DecidableEq`
-- structure needs a larger budget than the default.
set_option synthInstance.maxSize 400

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## Coordinate tensors -/











namespace ProjectiveSetting





variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}

/-! ## The strategy factor of a placement -/



/-- The placement of a difference is the difference of the placements. Paper
`14_analysis_of_the_pauli_basis_test.tex:420-450`, blueprint
`ch14_qpbt_observables.tex:1002-1031`. -/
theorem place_sub (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (p : _root_.MIPStarRE.QPBT.Placement)
    (O₁ O₂ : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace p.side)) :
    S.place p (O₁ - O₂) = S.place p O₁ - S.place p O₂ := by
  ext i j
  cases p <;> simp only [_root_.MIPStarRE.QPBT.ProjectiveSetting.place, Matrix.sub_apply, sub_mul, mul_sub]

/-! ## The action of a placement on the expanded state -/





/-! ## Opposite-placement bipartitions -/













/-! ## The four placements -/



























end ProjectiveSetting

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/ExtendedLines/Overlap.lean. -/
/-!
# Consistency of the extended-line measurements

This directly indexed auxiliary construction follows the first consistency
route for combined lines. The question carrier, completed answer alphabet,
and corrected error convention retain their existing meanings.

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











/-- On opposite registers a positive left effect preserves order in the right
effect. This applies to both directed player placements without exchanging spaces. -/
private theorem placed_overlap_mono {params : _root_.MIPStarRE.QPBT.AdmissibleParams} {error : ℝ}
    (setting : _root_.MIPStarRE.QPBT.ProjectiveSetting params error) (first second : _root_.MIPStarRE.QPBT.Placement)
    (hopposite : first.IsOpposite second)
    (left : _root_.LIDT.MIPStarRE.Quantum.Op (setting.ExpandedLocalSpace first.side))
    (lower upper : _root_.LIDT.MIPStarRE.Quantum.Op (setting.ExpandedLocalSpace second.side))
    (hleft : 0 ≤ left) (hright : lower ≤ upper) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm setting.psiHat (setting.place first left * setting.place second lower) ≤
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm setting.psiHat (setting.place first left * setting.place second upper) := by
  have hpositive := setting.place_mul_place_nonneg first second hopposite hleft
    (sub_nonneg.mpr hright)
  rw [setting.place_sub, mul_sub] at hpositive
  exact _root_.MIPStarRE.QPBT.DistanceCalculus.quadratic_form_mono (sub_nonneg.mp hpositive) setting.psiHat


















end

end MIPStarRE.QPBT

/-!
# Consistency of the extended-line measurements

This directly indexed auxiliary construction follows the first consistency
route for combined lines. The question carrier, completed answer alphabet,
and corrected error convention retain their existing meanings.

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

theorem solution {params : _root_.MIPStarRE.QPBT.AdmissibleParams}
    {error pointError lineError : ℝ} {setting : _root_.MIPStarRE.QPBT.ProjectiveSetting params error}
    {points : _root_.MIPStarRE.QPBT.CombinedPointsWitness setting pointError}
    (sublines : _root_.MIPStarRE.QPBT.SubLineWitness params) (lines : _root_.MIPStarRE.QPBT.CombinedLinesWitness setting points lineError)
    (first second : _root_.MIPStarRE.QPBT.Placement) (hopposite : first.IsOpposite second)
    (line : _root_.MIPStarRE.QPBT.DirectLineDesc params.extendedDirectLd)
    (point : Fin params.extendedDirectLd.m → _root_.MIPStarRE.QPBT.DirectScalarQ params.extendedDirectLd)
    (hpoint : point ∈ line.pointSet) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (sublines.conditionalLaw line) (fun sample =>
      ∑ pair, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm setting.psiHat
        (setting.place first ((lines.T first.side sample.val.2.1 sample.val.2.2).effect pair) *
          setting.place second (((points.Q second.side
            (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli params point))
            (_root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli params point))).postprocess
              (fun values => (some values.1, some values.2))).effect
                (_root_.MIPStarRE.QPBT.evalOpt sample.val.2.1 (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli params point)) pair.1,
                  _root_.MIPStarRE.QPBT.evalOpt sample.val.2.2 (_root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli params point)) pair.2)))) ≤
      _root_.MIPStarRE.QPBT.extendedPointOverlap setting points lines sublines first second (line, point) := by
  rw [_root_.MIPStarRE.QPBT.extendedPointOverlap, sublines.extendedMeasurement_overlap]
  apply _root_.LIDT.MIPStarRE.LDT.avgOver_mono
  intro sample
  apply Finset.sum_le_sum
  intro pair _
  apply placed_overlap_mono setting first second hopposite _ _ _
    ((lines.T first.side sample.val.2.1 sample.val.2.2).pos pair)
  have hline := (Finset.mem_filter.mp sample.property).2
  have hsample := (Finset.mem_filter.mp sample.property).1
  have hpointSample : point ∈ sample.val.1.pointSet := by rw [hline]; exact hpoint
  have hcomparison := sublines.completedPoint_effect_le sample.val hsample pair point hpointSample
    (points.Q second.side (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli params point))
      (_root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli params point)))
  rw [hline] at hcomparison
  exact hcomparison
