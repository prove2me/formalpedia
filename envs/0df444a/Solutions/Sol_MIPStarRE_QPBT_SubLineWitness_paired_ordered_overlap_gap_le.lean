-- Prove2me | solution 1 for MIPStarRE.QPBT.SubLineWitness.paired_ordered_overlap_gap_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:20:47.756528+00:00
-- url     : https://prove2.me/submissions/99974dd4-83f9-4627-8fc3-772ae2fbb75a

-- Generated proof for MIPStarRE.QPBT.SubLineWitness.paired_ordered_overlap_gap_le.
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
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Combining_Defs
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLines_Overlap
import Definitions.Def_QPBT_QPBT_Combining_Points_PlacementSupport
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Games_DistributionAux
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Support
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Observables_LineMeasurement_Expanded
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_CombinedPointsWitness_orderedZX_dist_le
import Theorems.Thm_MIPStarRE_QPBT_Distribution_prod_isProbability
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_sum_norm_place_completedPair_sub_sq
import Theorems.Thm_MIPStarRE_QPBT_SubLineWitness_avgOver_projX_projZ
import Theorems.Thm_MIPStarRE_QPBT_abs_overlap_gap_le_sqrt_of_opFamilyDistSq

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



























/-- The state quadratic form is additive over finite sums of operators. This is
the formalization-only identity `lem:distance-qform-finset-sum`, used to expand
the relabeled overlaps in `lem:ld-sandwich`; detailed source proof
`references/neexp-paper/05_quantum_preliminaries.tex:952-999`. -/
theorem stateQForm_finset_sum {β ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (s : Finset β) (M : β → _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (∑ b ∈ s, M b) = ∑ b ∈ s, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (M b) := by
  simp [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, _root_.MIPStarRE.QPBT.applyOperatorToState]































































end MIPStarRE.QPBT.DistanceCalculus

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





/-! ## The action of a placement on the expanded state -/

/-- The expanded state is the shuffle of the coordinate tensor of the strategy
state with the two EPR ancillas. This is `eq:def-psihat`, paper
`14_analysis_of_the_pauli_basis_test.tex:367-372`, blueprint
`ch14_qpbt_observables.tex:895-918`. -/
theorem psiHat_eq_reindexState (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) :
    S.psiHat = _root_.MIPStarRE.QPBT.reindexState (_root_.MIPStarRE.QPBT.sixRegShuffle P S.toStrategy.ιA S.toStrategy.ιB)
      (_root_.MIPStarRE.QPBT.vecTensor (_root_.MIPStarRE.QPBT.vecTensor S.toStrategy.ψ (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P)))
        (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P))) := rfl

/-- The expanded strategy state is normalized. -/
theorem psiHat_norm (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) : ‖S.psiHat‖ = 1 := by
  rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.psiHat_eq_reindexState, _root_.MIPStarRE.QPBT.reindexState_norm_eq, _root_.MIPStarRE.QPBT.vecTensor_norm_eq,
    _root_.MIPStarRE.QPBT.vecTensor_norm_eq, S.toStrategy.ψ_norm, _root_.MIPStarRE.QPBT.eprState_norm]
  norm_num

/-! ## Opposite-placement bipartitions -/













/-! ## The four placements -/



























end ProjectiveSetting

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







/-! ## Factorization of opposite placements with distinct Pauli factors -/













end ProjectiveSetting

/-! ## The overlap identity -/







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









/-- Postprocessing the left measurement groups, but does not alter, its overlap
with a family indexed by the postprocessed answer. -/
private theorem placed_overlap_postprocess {params : _root_.MIPStarRE.QPBT.AdmissibleParams} {error : ℝ}
    {Answer Output : Type*} [Fintype Answer] [DecidableEq Answer]
    [Fintype Output] [DecidableEq Output]
    (setting : _root_.MIPStarRE.QPBT.ProjectiveSetting params error) (first second : _root_.MIPStarRE.QPBT.Placement)
    (measurement : _root_.LIDT.MIPStarRE.Quantum.Measurement Answer (setting.ExpandedLocalSpace first.side))
    (mapping : Answer → Output) (right : Output → _root_.LIDT.MIPStarRE.Quantum.Op (setting.ExpandedLocalSpace second.side)) :
    (∑ output, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm setting.psiHat
      (setting.place first ((measurement.postprocess mapping).effect output) *
        setting.place second (right output))) =
      ∑ answer, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm setting.psiHat
        (setting.place first (measurement.effect answer) *
          setting.place second (right (mapping answer))) := by
  classical
  simp only [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect, setting.place_finsetSum,
    Finset.sum_mul, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_finset_sum]
  calc
    (∑ output, ∑ answer ∈ Finset.univ.filter (fun answer => mapping answer = output),
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm setting.psiHat (setting.place first (measurement.effect answer) *
          setting.place second (right output))) =
        ∑ output, ∑ answer ∈ Finset.univ.filter (fun answer => mapping answer = output),
          _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm setting.psiHat (setting.place first (measurement.effect answer) *
            setting.place second (right (mapping answer))) := by
      apply Finset.sum_congr rfl
      intro output _
      apply Finset.sum_congr rfl
      intro answer hanswer
      rw [(Finset.mem_filter.mp hanswer).2]
    _ = _ := Finset.sum_fiberwise _ _ _




















end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/ZEvalDeficit.lean. -/
/-!
# Z-point deficits of the evaluated pair-line measurement

This module bounds the deficit of the overlap between the evaluated paired-line
measurement and the expanded Z-point measurement. The proof inserts the completed
joint point measurement, replaces it by the X-then-Z ordered product, and sums
the X effects. It uses evaluated consistency and the distance from the joint
point measurement to that ordered product. The bound holds first over any
probability law on pairs of line-point pairs and then over a product of restricted
line-point laws, whose point marginal is the uniform pair.

The estimates hold for arbitrary opposite placements, with first-player
specializations; register commutation requires no symmetry of the state.
The completed-outcome and real-overlap lemmas are also available for other
calculations. The concrete X-deficit argument is separate, in
`MIPStarRE.QPBT.Combining.Lines.ConcreteXDeficit`.

## References

The Z deficit supports blueprint `lem:claim-17-3-re-direct`, alongside the
source `lem:claim-17-3`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1204-1239`; the
consistency input is `lem:qld-xz-lines` and the ordered products are those of
`lem:qld-4-10`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

noncomputable section

/-! ## Completed point pairs -/









namespace ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}







/-- The completed `Z`-then-`X` point product vanishes on both `none` classes
and restricts to the ordered product on evaluated pairs. -/
theorem completedPair_norm_sq_sum_ZX (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) {δ : ℝ}
    (points : _root_.MIPStarRE.QPBT.CombinedPointsWitness S δ) (p : _root_.MIPStarRE.QPBT.Placement)
    (x z : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) :
    (∑ o : Option (_root_.MIPStarRE.QPBT.PauliScalar P) × Option (_root_.MIPStarRE.QPBT.PauliScalar P),
        ‖_root_.MIPStarRE.QPBT.applyOperatorToState
          (S.place p (((points.Q p.side x z).postprocess (fun ab =>
              (some ab.1, some ab.2))).effect o) -
            S.place p
              ((S.pointMeasExpOption p.side .Z z).effect o.2 *
                (S.pointMeasExpOption p.side .X x).effect o.1))
          S.psiHat‖ ^ 2) =
      ∑ ab : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P,
        ‖_root_.MIPStarRE.QPBT.applyOperatorToState
          (S.place p ((points.Q p.side x z).effect ab) -
            S.place p
              ((S.pointMeasExp p.side .Z z).effect ab.2 *
                (S.pointMeasExp p.side .X x).effect ab.1))
          S.psiHat‖ ^ 2 := by
  refine S.sum_norm_place_completedPair_sub_sq p (points.Q p.side x z) _ _ ?_ ?_ ?_
  · intro ab
    rw [S.pointMeasExpOption_effect_some, S.pointMeasExpOption_effect_some]
  · intro o2
    rw [S.pointMeasExpOption_effect_none, mul_zero]
  · intro o1
    rw [S.pointMeasExpOption_effect_none, zero_mul]


end ProjectiveSetting

/-! ## The abstract one-point deficit -/



/-! ## The two placed deficits -/





/-! ## The two deficits over a product of restricted line-point laws -/











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
    (first second : _root_.MIPStarRE.QPBT.Placement) :
    |avgOver sublines.D (_root_.MIPStarRE.QPBT.pairedSublineOverlap setting points lines first second) -
      _root_.LIDT.MIPStarRE.LDT.avgOver sublines.D (_root_.MIPStarRE.QPBT.orderedSublineOverlap setting points lines first second)| ≤
        Real.sqrt (4 * pointError) := by
  let law := _root_.MIPStarRE.QPBT.Distribution.prod sublines.D
    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectScalarQ params.extendedDirectLd))
  let point (sample : _root_.MIPStarRE.QPBT.SubLineTriple params × _root_.MIPStarRE.QPBT.DirectScalarQ params.extendedDirectLd) :=
    _root_.MIPStarRE.QPBT.directPointToPauli params (sample.1.1.base + sample.2 • sample.1.1.direction)
  let lineMeasurement (sample : _root_.MIPStarRE.QPBT.SubLineTriple params × _root_.MIPStarRE.QPBT.DirectScalarQ params.extendedDirectLd) :=
    setting.placedMeasurement first
      ((lines.T first.side sample.1.2.1 sample.1.2.2).postprocess (fun pair =>
        (_root_.MIPStarRE.QPBT.evalOpt sample.1.2.1 (_root_.MIPStarRE.QPBT.projX (point sample)) pair.1,
          _root_.MIPStarRE.QPBT.evalOpt sample.1.2.2 (_root_.MIPStarRE.QPBT.projZ (point sample)) pair.2)))
  let joint (sample : _root_.MIPStarRE.QPBT.SubLineTriple params × _root_.MIPStarRE.QPBT.DirectScalarQ params.extendedDirectLd)
      (answer : Option (_root_.MIPStarRE.QPBT.PauliScalar params) × Option (_root_.MIPStarRE.QPBT.PauliScalar params)) :=
    setting.place second (((points.Q second.side (_root_.MIPStarRE.QPBT.projX (point sample))
      (_root_.MIPStarRE.QPBT.projZ (point sample))).postprocess (fun values => (some values.1, some values.2))).effect
        answer)
  let ordered (sample : _root_.MIPStarRE.QPBT.SubLineTriple params × _root_.MIPStarRE.QPBT.DirectScalarQ params.extendedDirectLd)
      (answer : Option (_root_.MIPStarRE.QPBT.PauliScalar params) × Option (_root_.MIPStarRE.QPBT.PauliScalar params)) :=
    setting.place second
      ((setting.pointMeasExpOption second.side .Z (_root_.MIPStarRE.QPBT.projZ (point sample))).effect answer.2 *
        (setting.pointMeasExpOption second.side .X (_root_.MIPStarRE.QPBT.projX (point sample))).effect answer.1)
  have hprob : law.IsProbability := _root_.MIPStarRE.QPBT.Distribution.prod_isProbability _ _ sublines.isProbability
    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_isProbability _)
  have hdist : _root_.MIPStarRE.QPBT.opFamilyDistSq law joint ordered setting.psiHat ≤ 4 * pointError := by
    unfold _root_.MIPStarRE.QPBT.opFamilyDistSq
    change _root_.LIDT.MIPStarRE.LDT.avgOver law (fun sample => ∑ answer,
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState (joint sample answer - ordered sample answer) setting.psiHat‖ ^ 2) ≤ _
    have hcompleted := _root_.LIDT.MIPStarRE.LDT.avgOver_congr law _ _ (fun sample =>
      setting.completedPair_norm_sq_sum_ZX points second
        (_root_.MIPStarRE.QPBT.projX (point sample)) (_root_.MIPStarRE.QPBT.projZ (point sample)))
    dsimp only [joint, ordered] at *
    rw [hcompleted]
    change _root_.LIDT.MIPStarRE.LDT.avgOver law (fun sample => ∑ answer : _root_.MIPStarRE.QPBT.PauliScalar params × _root_.MIPStarRE.QPBT.PauliScalar params,
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState
        (setting.place second ((points.Q second.side (_root_.MIPStarRE.QPBT.projX (point sample))
          (_root_.MIPStarRE.QPBT.projZ (point sample))).effect answer) -
          setting.place second
            ((setting.pointMeasExp second.side .Z (_root_.MIPStarRE.QPBT.projZ (point sample))).effect answer.2 *
              (setting.pointMeasExp second.side .X (_root_.MIPStarRE.QPBT.projX (point sample))).effect answer.1))
        setting.psiHat‖ ^ 2) ≤ _
    rw [show law = _root_.MIPStarRE.QPBT.Distribution.prod sublines.D
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectScalarQ params.extendedDirectLd)) from rfl,
      _root_.MIPStarRE.QPBT.SandwichProduct.avgOver_distribution_prod]
    dsimp only [point]
    rw [_root_.MIPStarRE.QPBT.SubLineWitness.avgOver_projX_projZ params sublines
      (fun coordinates => ∑ answer : _root_.MIPStarRE.QPBT.PauliScalar params × _root_.MIPStarRE.QPBT.PauliScalar params,
        ‖_root_.MIPStarRE.QPBT.applyOperatorToState
          (setting.place second ((points.Q second.side coordinates.1 coordinates.2).effect answer) -
            setting.place second
              ((setting.pointMeasExp second.side .Z coordinates.2).effect answer.2 *
                (setting.pointMeasExp second.side .X coordinates.1).effect answer.1))
          setting.psiHat‖ ^ 2)]
    exact points.orderedZX_dist_le second
  have hgap := _root_.MIPStarRE.QPBT.abs_overlap_gap_le_sqrt_of_opFamilyDistSq law lineMeasurement joint ordered
    setting.psiHat hprob setting.psiHat_norm (4 * pointError) hdist
  have hregroup (right : (_root_.MIPStarRE.QPBT.SubLineTriple params × _root_.MIPStarRE.QPBT.DirectScalarQ params.extendedDirectLd) →
      Option (_root_.MIPStarRE.QPBT.PauliScalar params) × Option (_root_.MIPStarRE.QPBT.PauliScalar params) →
        _root_.LIDT.MIPStarRE.Quantum.Op (setting.ExpandedLocalSpace second.side)) :
      _root_.LIDT.MIPStarRE.LDT.avgOver law (fun sample => ∑ answer, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm setting.psiHat
        ((lineMeasurement sample).effect answer * setting.place second (right sample answer))) =
      _root_.LIDT.MIPStarRE.LDT.avgOver sublines.D (fun sample =>
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectScalarQ params.extendedDirectLd)) (fun parameter =>
          ∑ pair, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm setting.psiHat
            (setting.place first ((lines.T first.side sample.2.1 sample.2.2).effect pair) *
              setting.place second (right (sample, parameter)
                (_root_.MIPStarRE.QPBT.evalOpt sample.2.1 (_root_.MIPStarRE.QPBT.projX (point (sample, parameter))) pair.1,
                  _root_.MIPStarRE.QPBT.evalOpt sample.2.2 (_root_.MIPStarRE.QPBT.projZ (point (sample, parameter))) pair.2))))) := by
    change _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.Distribution.prod sublines.D
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectScalarQ params.extendedDirectLd))) _ = _
    rw [_root_.MIPStarRE.QPBT.SandwichProduct.avgOver_distribution_prod]
    apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
    intro sample
    apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
    intro parameter
    exact placed_overlap_postprocess setting first second _ _ _
  dsimp only [joint, ordered] at hgap
  rw [hregroup, hregroup] at hgap
  exact hgap
