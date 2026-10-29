-- Prove2me | solution 1 for MIPStarRE.QPBT.ExtendedLineGame.axis_same_line_evaluation_defect_le_branch_chain
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T02:18:01.44424+00:00
-- url     : https://prove2.me/submissions/e0e37bce-0955-46f6-ac42-1f6ab8b6c230

-- Generated proof for MIPStarRE.QPBT.ExtendedLineGame.axis_same_line_evaluation_defect_le_branch_chain.
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
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_GameValue
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame_EvaluatedLineComparison
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame_LinePointRejection
import Definitions.Def_QPBT_QPBT_Combining_Points
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_TensorSupport
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_LIDT_MIPStarRE_Quantum_Measurement_postprocess_comp
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_aline_point_rejection_eq_completedLinePointDefect
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_completed_defect_eq_read_defect
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_point_aline_rejection_eq_completedLinePointDefect
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_point_branch_rejection_eq_consistencyDefect
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_reversed_axis_completed_defect_eq_read_defect
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_congr
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_trans_le

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.ExtendedLineGame
end MIPStarRE.QPBT.ExtendedLineGame
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting

/- Source helpers from QPBT/Combining/ExtendedLineGame/PointPointRejection.lean. -/
/-!
# Point/point rejection for the extended direct game

This module bounds the point-agreement branch of the directly indexed
low-degree strategy by the self-consistency error of the supplied joint point
measurements.  The common extended point is transported by one coordinate
equivalence to the jointly uniform tuple `(x, z, alpha, beta)` before the
scalar coarse-graining is applied.

This is a formalization-only auxiliary for the supplied-witness route in the
proof of `lem:qld-4-7`; it does not construct the point witness or establish
the complete passing-value estimate.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:689-709`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`
- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-311`
- Issue Dengnifer/MIPStarRE-QPBT-bak#313.
-/

@[expose] public section

open scoped BigOperators MatrixOrder ComplexOrder

set_option synthInstance.maxSize 400

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum
open ProjectiveSetting

noncomputable section

namespace ExtendedLineGame

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
variable {setting : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon}
variable {points : _root_.MIPStarRE.QPBT.CombinedPointsWitness setting deltaQ}

















/-- The completed point read of the direct-game answer measurement is the
corresponding scalar coarse-graining of the supplied joint point measurement. -/
theorem point_read_effect
    (lines : _root_.MIPStarRE.QPBT.ExtendedLinesWitness setting points deltaL) (side : _root_.MIPStarRE.QPBT.PlayerSide)
    (sample : _root_.MIPStarRE.QPBT.DirectLdSpace P.extendedDirectLd) (answer : Option (_root_.MIPStarRE.QPBT.PauliScalar P)) :
    (((_root_.MIPStarRE.QPBT.ExtendedLineGame.answerMeasurement lines side
        (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample)).postprocess
      _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead).effect answer) =
      ((points.Q side
        (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P sample.point))
        (_root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P sample.point))).postprocess fun values =>
          some (_root_.MIPStarRE.QPBT.directPointToPauli P sample.point (_root_.MIPStarRE.QPBT.alphaVar P.m) * values.1 +
            _root_.MIPStarRE.QPBT.directPointToPauli P sample.point (_root_.MIPStarRE.QPBT.betaVar P.m) * values.2)).effect answer := by
  classical
  unfold _root_.MIPStarRE.QPBT.ExtendedLineGame.answerMeasurement _root_.MIPStarRE.QPBT.CombinedPointsWitness.extendedQ
  rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_comp,
    _root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_comp]
  rfl





end ExtendedLineGame

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/ExtendedLineGame/EvaluatedLineComparison.lean. -/
/-!
# Completed same-line evaluation comparison

This module compares Alice's and Bob's completed axis-line or diagonal-line
readouts through the corresponding point readouts. The comparison uses the
consistency triangle on the common direct-game sample and then applies the
already proved mixed and point/point branch bounds.

The readouts take values in `Option (PauliScalar P)`. Agreement on `none`, in
particular for zero directions, is not an equality of parameter evaluations;
no coefficient-collision conclusion is asserted here.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`
- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:389-401`
- Blueprint `lem:qld-4-7`.
- Issue Dengnifer/MIPStarRE-QPBT-bak#321.
-/

@[expose] public section

open scoped BigOperators MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace ExtendedLineGame

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
variable {setting : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon}
variable {points : _root_.MIPStarRE.QPBT.CombinedPointsWitness setting deltaQ}

/-- A uniform consistency defect whose integrand uses only the first
coordinate of a product equivalence has the corresponding uniform marginal. -/
private theorem consistencyDefect_uniform_equiv_fst
    {Gamma X Y Alpha I : Type*}
    [Fintype Gamma] [DecidableEq Gamma] [Nonempty Gamma]
    [Fintype X] [DecidableEq X] [Nonempty X]
    [Finite Y] [Nonempty Y]
    [Fintype Alpha] [DecidableEq Alpha]
    [Fintype I] [DecidableEq I]
    (e : Gamma ≃ X × Y) (A B : X → Alpha → _root_.LIDT.MIPStarRE.Quantum.Op I)
    (psi : EuclideanSpace ℂ I) :
    _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Gamma)
        (fun sample answer => A (e sample).1 answer)
        (fun sample answer => B (e sample).1 answer) psi =
      _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution X) A B psi := by
  unfold _root_.MIPStarRE.QPBT.consistencyDefect
  let f : X → ℝ := fun x =>
    ∑ a : Alpha, ∑ b : Alpha,
      if a = b then 0 else
        (inner ℂ psi ((EuclideanSpace.equiv I ℂ).symm
          ((A x a * B x b).mulVec psi))).re
  change _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Gamma) (fun sample => f (e sample).1) =
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution X) f
  exact _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_equiv_fst e f





/-- The point/point read defect is unchanged when the jointly uniform direct
sample's unused index and direction are retained. -/
private theorem point_read_defect_on_direct_samples_eq_rejection
    (lines : _root_.MIPStarRE.QPBT.ExtendedLinesWitness setting points deltaL) :
    _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectLdSpace P.extendedDirectLd))
        (fun sample answer => _root_.MIPStarRE.QPBT.heteroKron
          (((_root_.MIPStarRE.QPBT.ExtendedLineGame.answerMeasurement lines .alice
            (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample)).postprocess
              _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead).effect answer) 1)
        (fun sample answer => _root_.MIPStarRE.QPBT.heteroKron 1
          (((_root_.MIPStarRE.QPBT.ExtendedLineGame.answerMeasurement lines .bob
            (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample)).postprocess
              _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead).effect answer))
        (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState setting) =
      _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability P.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
        (.point, .point) := by
  rw [_root_.MIPStarRE.QPBT.ExtendedLineGame.point_branch_rejection_eq_consistencyDefect lines]
  calc
    _ = _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectLdSpace P.extendedDirectLd))
        (fun sample answer => _root_.MIPStarRE.QPBT.heteroKron
          (((points.Q .alice
            (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P sample.point))
            (_root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P sample.point))).postprocess fun values =>
              some (_root_.MIPStarRE.QPBT.directPointToPauli P sample.point (_root_.MIPStarRE.QPBT.alphaVar P.m) * values.1 +
                _root_.MIPStarRE.QPBT.directPointToPauli P sample.point (_root_.MIPStarRE.QPBT.betaVar P.m) * values.2)).effect answer) 1)
        (fun sample answer => _root_.MIPStarRE.QPBT.heteroKron 1
          (((points.Q .bob
            (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P sample.point))
            (_root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P sample.point))).postprocess fun values =>
              some (_root_.MIPStarRE.QPBT.directPointToPauli P sample.point (_root_.MIPStarRE.QPBT.alphaVar P.m) * values.1 +
                _root_.MIPStarRE.QPBT.directPointToPauli P sample.point (_root_.MIPStarRE.QPBT.betaVar P.m) * values.2)).effect answer))
        (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState setting) := by
      apply _root_.MIPStarRE.QPBT.consistencyDefect_congr <;> intro sample answer
      · rw [_root_.MIPStarRE.QPBT.ExtendedLineGame.point_read_effect lines .alice]
      · rw [_root_.MIPStarRE.QPBT.ExtendedLineGame.point_read_effect lines .bob]
    _ = _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution
          (Fin P.extendedDirectLd.m → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd))
        (fun point answer => _root_.MIPStarRE.QPBT.heteroKron
          (((points.Q .alice
            (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P point))
            (_root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P point))).postprocess fun values =>
              some (_root_.MIPStarRE.QPBT.directPointToPauli P point (_root_.MIPStarRE.QPBT.alphaVar P.m) * values.1 +
                _root_.MIPStarRE.QPBT.directPointToPauli P point (_root_.MIPStarRE.QPBT.betaVar P.m) * values.2)).effect answer) 1)
        (fun point answer => _root_.MIPStarRE.QPBT.heteroKron 1
          (((points.Q .bob
            (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P point))
            (_root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P point))).postprocess fun values =>
              some (_root_.MIPStarRE.QPBT.directPointToPauli P point (_root_.MIPStarRE.QPBT.alphaVar P.m) * values.1 +
                _root_.MIPStarRE.QPBT.directPointToPauli P point (_root_.MIPStarRE.QPBT.betaVar P.m) * values.2)).effect answer))
        (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState setting) := by
      exact consistencyDefect_uniform_equiv_fst
        (Gamma := _root_.MIPStarRE.QPBT.DirectLdSpace P.extendedDirectLd)
        (X := Fin P.extendedDirectLd.m → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd)
        (Y := Fin P.extendedDirectLd.m ×
          (Fin P.extendedDirectLd.m → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd))
        (Alpha := Option (_root_.MIPStarRE.QPBT.PauliScalar P))
        (I := setting.ExpandedLocalSpace .alice × setting.ExpandedLocalSpace .bob)
        (_root_.MIPStarRE.QPBT.directLdSpacePointEquiv P.extendedDirectLd)
        (fun point answer => _root_.MIPStarRE.QPBT.heteroKron
          (((points.Q .alice
            (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P point))
            (_root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P point))).postprocess fun values =>
              some (_root_.MIPStarRE.QPBT.directPointToPauli P point (_root_.MIPStarRE.QPBT.alphaVar P.m) * values.1 +
                _root_.MIPStarRE.QPBT.directPointToPauli P point (_root_.MIPStarRE.QPBT.betaVar P.m) * values.2)).effect answer) 1)
        (fun point answer => _root_.MIPStarRE.QPBT.heteroKron 1
          (((points.Q .bob
            (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P point))
            (_root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P point))).postprocess fun values =>
              some (_root_.MIPStarRE.QPBT.directPointToPauli P point (_root_.MIPStarRE.QPBT.alphaVar P.m) * values.1 +
                _root_.MIPStarRE.QPBT.directPointToPauli P point (_root_.MIPStarRE.QPBT.betaVar P.m) * values.2)).effect answer))
        (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState setting)









end ExtendedLineGame

end

end MIPStarRE.QPBT

/-!
# Completed same-line evaluation comparison

This module compares Alice's and Bob's completed axis-line or diagonal-line
readouts through the corresponding point readouts. The comparison uses the
consistency triangle on the common direct-game sample and then applies the
already proved mixed and point/point branch bounds.

The readouts take values in `Option (PauliScalar P)`. Agreement on `none`, in
particular for zero directions, is not an equality of parameter evaluations;
no coefficient-collision conclusion is asserted here.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`
- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:389-401`
- Blueprint `lem:qld-4-7`.
- Issue Dengnifer/MIPStarRE-QPBT-bak#321.
-/



open scoped BigOperators MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum



open MIPStarRE.QPBT.ExtendedLineGame

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
variable {setting : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon}
variable {points : _root_.MIPStarRE.QPBT.CombinedPointsWitness setting deltaQ}

theorem solution
    (lines : _root_.MIPStarRE.QPBT.ExtendedLinesWitness setting points deltaL) :
    _root_.MIPStarRE.QPBT.ExtendedLineGame.axisSameLineEvaluationDefect lines ≤
      _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability P.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
          (.aline, .point) +
        2 * Real.sqrt
          (_root_.MIPStarRE.QPBT.directLdBranchRejectionProbability P.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
              (.point, .point) +
            _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability P.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
              (.point, .aline)) := by
  let μ := _root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectLdSpace P.extendedDirectLd)
  let A : _root_.MIPStarRE.QPBT.DirectLdSpace P.extendedDirectLd →
      _root_.LIDT.MIPStarRE.Quantum.Measurement (Option (_root_.MIPStarRE.QPBT.PauliScalar P))
        (setting.ExpandedLocalSpace .alice × setting.ExpandedLocalSpace .bob) :=
    fun sample => _root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement
      (ιB := setting.ExpandedLocalSpace .bob)
      ((_root_.MIPStarRE.QPBT.ExtendedLineGame.answerMeasurement lines .alice
        (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample)).postprocess
          (_root_.MIPStarRE.QPBT.ExtendedLineGame.axisGameRead sample))
  let B : _root_.MIPStarRE.QPBT.DirectLdSpace P.extendedDirectLd →
      _root_.LIDT.MIPStarRE.Quantum.Measurement (Option (_root_.MIPStarRE.QPBT.PauliScalar P))
        (setting.ExpandedLocalSpace .alice × setting.ExpandedLocalSpace .bob) :=
    fun sample => _root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement
      (ιA := setting.ExpandedLocalSpace .alice)
      ((_root_.MIPStarRE.QPBT.ExtendedLineGame.answerMeasurement lines .bob
        (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample)).postprocess _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead)
  let C : _root_.MIPStarRE.QPBT.DirectLdSpace P.extendedDirectLd →
      _root_.LIDT.MIPStarRE.Quantum.Measurement (Option (_root_.MIPStarRE.QPBT.PauliScalar P))
        (setting.ExpandedLocalSpace .alice × setting.ExpandedLocalSpace .bob) :=
    fun sample => _root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement
      (ιB := setting.ExpandedLocalSpace .bob)
      ((_root_.MIPStarRE.QPBT.ExtendedLineGame.answerMeasurement lines .alice
        (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample)).postprocess _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead)
  let D : _root_.MIPStarRE.QPBT.DirectLdSpace P.extendedDirectLd →
      _root_.LIDT.MIPStarRE.Quantum.Measurement (Option (_root_.MIPStarRE.QPBT.PauliScalar P))
        (setting.ExpandedLocalSpace .alice × setting.ExpandedLocalSpace .bob) :=
    fun sample => _root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement
      (ιA := setting.ExpandedLocalSpace .alice)
      ((_root_.MIPStarRE.QPBT.ExtendedLineGame.answerMeasurement lines .bob
        (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample)).postprocess
          (_root_.MIPStarRE.QPBT.ExtendedLineGame.axisGameRead sample))
  have hAB : _root_.MIPStarRE.QPBT.consistencyDefect μ (fun sample answer => (A sample).effect answer)
      (fun sample answer => (B sample).effect answer) (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState setting) ≤
      _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability P.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
        (.aline, .point) := by
    change _root_.MIPStarRE.QPBT.consistencyDefect μ
      (fun sample answer => _root_.MIPStarRE.QPBT.heteroKron
        (((_root_.MIPStarRE.QPBT.ExtendedLineGame.answerMeasurement lines .alice
          (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample)).postprocess
            (_root_.MIPStarRE.QPBT.ExtendedLineGame.axisGameRead sample)).effect answer) 1)
      (fun sample answer => _root_.MIPStarRE.QPBT.heteroKron 1
        (((_root_.MIPStarRE.QPBT.ExtendedLineGame.answerMeasurement lines .bob
          (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample)).postprocess
            _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead).effect answer)) (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState setting) ≤ _
    rw [← _root_.MIPStarRE.QPBT.ExtendedLineGame.completed_defect_eq_read_defect lines,
      ← _root_.MIPStarRE.QPBT.ExtendedLineGame.aline_point_rejection_eq_completedLinePointDefect lines]
  have hCB : _root_.MIPStarRE.QPBT.consistencyDefect μ (fun sample answer => (C sample).effect answer)
      (fun sample answer => (B sample).effect answer) (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState setting) ≤
      _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability P.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
        (.point, .point) := by
    change _root_.MIPStarRE.QPBT.consistencyDefect μ
      (fun sample answer => _root_.MIPStarRE.QPBT.heteroKron
        (((_root_.MIPStarRE.QPBT.ExtendedLineGame.answerMeasurement lines .alice
          (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample)).postprocess
            _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead).effect answer) 1)
      (fun sample answer => _root_.MIPStarRE.QPBT.heteroKron 1
        (((_root_.MIPStarRE.QPBT.ExtendedLineGame.answerMeasurement lines .bob
          (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample)).postprocess
            _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead).effect answer)) (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState setting) ≤ _
    exact le_of_eq (point_read_defect_on_direct_samples_eq_rejection lines)
  have hCD : _root_.MIPStarRE.QPBT.consistencyDefect μ (fun sample answer => (C sample).effect answer)
      (fun sample answer => (D sample).effect answer) (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState setting) ≤
      _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability P.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
        (.point, .aline) := by
    change _root_.MIPStarRE.QPBT.consistencyDefect μ
      (fun sample answer => _root_.MIPStarRE.QPBT.heteroKron
        (((_root_.MIPStarRE.QPBT.ExtendedLineGame.answerMeasurement lines .alice
          (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample)).postprocess
            _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead).effect answer) 1)
      (fun sample answer => _root_.MIPStarRE.QPBT.heteroKron 1
        (((_root_.MIPStarRE.QPBT.ExtendedLineGame.answerMeasurement lines .bob
          (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample)).postprocess
            (_root_.MIPStarRE.QPBT.ExtendedLineGame.axisGameRead sample)).effect answer)) (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState setting) ≤ _
    rw [← _root_.MIPStarRE.QPBT.ExtendedLineGame.reversed_axis_completed_defect_eq_read_defect lines,
      ← _root_.MIPStarRE.QPBT.ExtendedLineGame.point_aline_rejection_eq_completedLinePointDefect lines]
  change _root_.MIPStarRE.QPBT.consistencyDefect μ (fun sample answer => (A sample).effect answer)
    (fun sample answer => (D sample).effect answer) (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState setting) ≤ _
  exact _root_.MIPStarRE.QPBT.consistencyDefect_trans_le μ A B C D (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState setting) _ _ _
    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_isProbability _) (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState_norm setting) hAB hCB hCD
