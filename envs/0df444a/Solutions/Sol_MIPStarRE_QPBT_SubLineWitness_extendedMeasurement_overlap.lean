-- Prove2me | solution 1 for MIPStarRE.QPBT.SubLineWitness.extendedMeasurement_overlap
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:51:53.806622+00:00
-- url     : https://prove2.me/submissions/586307f5-fb91-4c5a-88a6-f59a7eda9ec0

-- Generated proof for MIPStarRE.QPBT.SubLineWitness.extendedMeasurement_overlap.
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
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLines_Measurement
import Definitions.Def_QPBT_QPBT_Combining_Points_PlacementSupport
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_CommutingObs
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow

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
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

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

/- Source helpers from QPBT/Observables/WinImplications/CommutingObs.lean. -/
attribute [local instance] _root_.MIPStarRE.QPBT.WinImplications.pauliEdgeNonemptyCommObs
/-!
# Approximate commutation of the point observables on commuting tuples

This module carries out the commuting half of the proof of Equation
`eq:pts-obs-commutation` in `lem:qld-win-implications-obs`: the chain of
consistency relations `eq:lc-11`, the commutation analysis
`lem:commutation-analysis`, and the expansion `eq:lc-12` of the observables in
terms of the trace-coarse-grained point projections.

## References

The declarations support `lem:qld-win-implications-obs` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:761-794`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:309-341`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace WinImplications



/-! ## Algebraic preliminaries -/







/-! ## Pair/W self-consistency on commuting tuples -/





/-! ## The chained relation of Equation `eq:lc-11` -/



/-! ## The commutation analysis on commuting tuples -/









/-! ## From projections to observables -/

/-- Applying a scaled operator scales the resulting state. Formalization-only
support for `eq:lc-12`, paper
`14_analysis_of_the_pauli_basis_test.tex:330-341`. -/
theorem applyOperatorToState_smul_op {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ℂ) (M : _root_.LIDT.MIPStarRE.Quantum.Op ι) (v : EuclideanSpace ℂ ι) :
    _root_.MIPStarRE.QPBT.applyOperatorToState (c • M) v = c • _root_.MIPStarRE.QPBT.applyOperatorToState M v := by
  unfold _root_.MIPStarRE.QPBT.applyOperatorToState
  rw [map_smul, LinearMap.smul_apply]







end WinImplications

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





/-- Real scalar multiplication commutes with placement. -/
private theorem place_real_smul {params : _root_.MIPStarRE.QPBT.AdmissibleParams} {error : ℝ}
    (setting : _root_.MIPStarRE.QPBT.ProjectiveSetting params error) (placement : _root_.MIPStarRE.QPBT.Placement) (scalar : ℝ)
    (operator : _root_.LIDT.MIPStarRE.Quantum.Op (setting.ExpandedLocalSpace placement.side)) :
    setting.place placement (scalar • operator) = scalar • setting.place placement operator := by
  ext row column
  cases placement <;> simp only [_root_.MIPStarRE.QPBT.ProjectiveSetting.place, Matrix.smul_apply, Complex.real_smul] <;>
    ring

/-- A placed overlap is linear in an averaged left operator. -/
private theorem placed_overlap_average {params : _root_.MIPStarRE.QPBT.AdmissibleParams} {error : ℝ}
    {Sample : Type*} (setting : _root_.MIPStarRE.QPBT.ProjectiveSetting params error) (first second : _root_.MIPStarRE.QPBT.Placement)
    (law : _root_.LIDT.MIPStarRE.LDT.Distribution Sample) (family : Sample → _root_.LIDT.MIPStarRE.Quantum.Op (setting.ExpandedLocalSpace first.side))
    (right : _root_.LIDT.MIPStarRE.Quantum.Op (setting.ExpandedLocalSpace second.side)) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm setting.psiHat
      (setting.place first (_root_.LIDT.MIPStarRE.LDT.averageOperatorOverDistribution law family) *
        setting.place second right) =
      _root_.LIDT.MIPStarRE.LDT.avgOver law (fun sample => _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm setting.psiHat
        (setting.place first (family sample) * setting.place second right)) := by
  unfold _root_.LIDT.MIPStarRE.LDT.averageOperatorOverDistribution _root_.LIDT.MIPStarRE.LDT.avgOver
  rw [setting.place_finsetSum, Finset.sum_mul, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_finset_sum]
  apply Finset.sum_congr rfl
  intro sample _
  rw [place_real_smul, smul_mul_assoc]
  have hscalar (operator : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.SixReg params setting.toStrategy.ιA setting.toStrategy.ιB)) :
      law.weight sample • operator = (law.weight sample : ℂ) • operator := by
    ext row column
    simp [Complex.real_smul]
  rw [hscalar]
  simp only [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, _root_.MIPStarRE.QPBT.WinImplications.applyOperatorToState_smul_op, inner_smul_right,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

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
    (first second : _root_.MIPStarRE.QPBT.Placement) (line : _root_.MIPStarRE.QPBT.DirectLineDesc params.extendedDirectLd)
    (point : Fin params.extendedDirectLd.m → _root_.MIPStarRE.QPBT.DirectScalarQ params.extendedDirectLd)
    (right : Option (_root_.MIPStarRE.QPBT.PauliScalar params) → _root_.LIDT.MIPStarRE.Quantum.Op (setting.ExpandedLocalSpace second.side)) :
    (∑ answer, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm setting.psiHat
      (setting.place first (((sublines.extendedMeasurement lines first.side line).postprocess
        (fun polynomial => (_root_.MIPStarRE.QPBT.directEvalOpt line point polynomial).map
          (_root_.MIPStarRE.QPBT.extendedDirectScalarEquiv params))).effect answer) *
            setting.place second (right answer))) =
      _root_.LIDT.MIPStarRE.LDT.avgOver (sublines.conditionalLaw line) (fun sample =>
        ∑ pair, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm setting.psiHat
          (setting.place first ((lines.T first.side sample.val.2.1 sample.val.2.2).effect pair) *
            setting.place second (right ((_root_.MIPStarRE.QPBT.directEvalOpt line point
              (sublines.combinedPolynomial sample.val
                (Finset.mem_filter.mp sample.property).1 pair)).map
                  (_root_.MIPStarRE.QPBT.extendedDirectScalarEquiv params))))) := by
  rw [placed_overlap_postprocess]
  change (∑ polynomial, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm setting.psiHat
    (setting.place first (_root_.LIDT.MIPStarRE.LDT.averageOperatorOverDistribution (sublines.conditionalLaw line)
      (fun sample => ((lines.T first.side sample.val.2.1 sample.val.2.2).postprocess
        (sublines.combinedPolynomial sample.val
          (Finset.mem_filter.mp sample.property).1)).effect polynomial)) *
      setting.place second (right ((_root_.MIPStarRE.QPBT.directEvalOpt line point polynomial).map
        (_root_.MIPStarRE.QPBT.extendedDirectScalarEquiv params))))) = _
  simp_rw [placed_overlap_average]
  rw [← _root_.LIDT.MIPStarRE.LDT.avgOver_sum]
  apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
  intro sample
  exact placed_overlap_postprocess setting first second _ _ _
