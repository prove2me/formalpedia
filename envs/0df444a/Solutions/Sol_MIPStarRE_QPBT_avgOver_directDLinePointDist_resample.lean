-- Prove2me | solution 1 for MIPStarRE.QPBT.avgOver_directDLinePointDist_resample
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:25:06.51993+00:00
-- url     : https://prove2.me/submissions/c6d040ab-0dcb-401b-85ec-b1e150648d3f

-- Generated proof for MIPStarRE.QPBT.avgOver_directDLinePointDist_resample.
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
import Definitions.Def_QPBT_QPBT_Algebra_Lines
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_LineResampling
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Questions
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Mathlib

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/DirectLowDegree/Transport/LineResampling.lean. -/
/-!
# Affine resampling of directly indexed lines

This module identifies the joint directly indexed line-point laws with the
equivalent sampling procedure that first draws their line marginal and then a
uniform affine parameter.  The argument retains zero diagonal directions: it
uses only translations of finite affine spaces and never cancels a direction.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:243-287`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1116`
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

noncomputable section







/-- Uniformly resampling a canonical affine line by a scalar parameter
recovers its original joint line-point sample. -/
private theorem avgOver_directLinePoint_resample
    (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (directionOf : Fin D.m → (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) →
      (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
    (lineOf : _root_.MIPStarRE.QPBT.DirectLdSpace D → _root_.MIPStarRE.QPBT.DirectLineDesc D)
    (hbase : ∀ sample,
      (lineOf sample).base =
        _root_.MIPStarRE.QPBT.lineRepMap (directionOf sample.index sample.direction) sample.point)
    (hdirection : ∀ sample,
      (lineOf sample).direction = directionOf sample.index sample.direction)
    (hline : ∀ sample t,
      lineOf (directLdSpacePointTranslateEquiv D directionOf t sample) =
        lineOf sample)
    (F : (_root_.MIPStarRE.QPBT.DirectLineDesc D × (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D)) → _root_.LIDT.MIPStarRE.LDT.Error) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectLdSpace D)) (fun sample =>
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectScalarQ D)) (fun t =>
          F (lineOf sample,
            (lineOf sample).base + t • (lineOf sample).direction))) =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectLdSpace D)) (fun sample =>
        F (lineOf sample, sample.point)) := by
  have hparameter : ∀ sample,
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectScalarQ D)) (fun t =>
          F (lineOf sample,
            (lineOf sample).base + t • (lineOf sample).direction)) =
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectScalarQ D)) (fun t =>
          F (lineOf sample,
            sample.point +
              t • directionOf sample.index sample.direction)) := by
    intro sample
    let direction := directionOf sample.index sample.direction
    let r := _root_.MIPStarRE.QPBT.directLineRepParameter direction sample.point
    calc
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectScalarQ D)) (fun t =>
          F (lineOf sample,
            (lineOf sample).base + t • (lineOf sample).direction)) =
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectScalarQ D)) (fun t =>
            F (lineOf sample,
              (lineOf sample).base +
                ((Equiv.addRight (-r)).symm t) •
                  (lineOf sample).direction)) :=
        _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_equiv (Equiv.addRight (-r)) _
      _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectScalarQ D)) (fun t =>
          F (lineOf sample,
            sample.point +
              t • directionOf sample.index sample.direction)) := by
        apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
        intro t
        congr 2
        rw [hdirection, hbase]
        have hadd : (Equiv.addRight (-r)).symm t = t + r := by
          simp
        rw [hadd]
        change _root_.MIPStarRE.QPBT.lineRepMap direction sample.point + (t + r) • direction =
          sample.point + t • direction
        rw [add_comm t r, add_smul, ← add_assoc,
          ← _root_.MIPStarRE.QPBT.directLineRepParameter_spec direction sample.point]
  have hsample : ∀ t : _root_.MIPStarRE.QPBT.DirectScalarQ D,
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectLdSpace D)) (fun sample =>
          F (lineOf sample,
            sample.point +
              t • directionOf sample.index sample.direction)) =
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectLdSpace D)) (fun sample =>
          F (lineOf sample, sample.point)) := by
    intro t
    calc
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectLdSpace D)) (fun sample =>
          F (lineOf sample,
            sample.point +
              t • directionOf sample.index sample.direction)) =
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectLdSpace D)) (fun sample =>
            F (lineOf ((directLdSpacePointTranslateEquiv D directionOf t).symm sample),
              ((directLdSpacePointTranslateEquiv D directionOf t).symm sample).point +
                t • directionOf
                  ((directLdSpacePointTranslateEquiv D directionOf t).symm sample).index
                  ((directLdSpacePointTranslateEquiv D directionOf t).symm sample).direction)) :=
        _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_equiv (directLdSpacePointTranslateEquiv D directionOf t) _
      _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectLdSpace D)) (fun sample =>
          F (lineOf sample, sample.point)) := by
        apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
        intro sample
        congr 2
        · change lineOf (directLdSpacePointTranslateEquiv D directionOf (-t) sample) =
            lineOf sample
          exact hline sample (-t)
        · rw [directLdSpacePointTranslateEquiv_symm_apply]
          simp [add_assoc]
  calc
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectLdSpace D)) (fun sample =>
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectScalarQ D)) (fun t =>
          F (lineOf sample,
            (lineOf sample).base + t • (lineOf sample).direction))) =
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectLdSpace D)) (fun sample =>
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectScalarQ D)) (fun t =>
            F (lineOf sample,
              sample.point +
                t • directionOf sample.index sample.direction))) := by
      apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
      exact hparameter
    _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectScalarQ D)) (fun t =>
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectLdSpace D)) (fun sample =>
          F (lineOf sample,
            sample.point +
              t • directionOf sample.index sample.direction))) :=
      _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_comm _
    _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectScalarQ D)) (fun _ =>
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectLdSpace D)) (fun sample =>
          F (lineOf sample, sample.point))) := by
      apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
      exact hsample
    _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectLdSpace D)) (fun sample =>
        F (lineOf sample, sample.point)) := _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_const _





end

end MIPStarRE.QPBT

/-!
# Affine resampling of directly indexed lines

This module identifies the joint directly indexed line-point laws with the
equivalent sampling procedure that first draws their line marginal and then a
uniform affine parameter.  The argument retains zero diagonal directions: it
uses only translations of finite affine spaces and never cancels a direction.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:243-287`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1116`
-/



open scoped BigOperators

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

theorem solution
    (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (F : (_root_.MIPStarRE.QPBT.DirectLineDesc D × (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D)) → _root_.LIDT.MIPStarRE.LDT.Error) :
    _root_.LIDT.MIPStarRE.LDT.avgOver ((_root_.MIPStarRE.QPBT.directDLinePointDist D).map Prod.fst) (fun line =>
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectScalarQ D)) (fun t =>
          F (line, line.base + t • line.direction))) =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.directDLinePointDist D) F := by
  simp only [_root_.MIPStarRE.QPBT.directDLinePointDist, _root_.LIDT.MIPStarRE.LDT.Distribution.avgOver_map]
  apply avgOver_directLinePoint_resample D
      (fun (index : Fin D.m) (direction : Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) =>
        _root_.MIPStarRE.QPBT.directPrefixProjection index direction)
      (_root_.MIPStarRE.QPBT.directDLineDescOf D)
  · intro sample
    rfl
  · intro sample
    rfl
  · intro sample t
    rw [directLdSpacePointTranslateEquiv_apply]
    simp only [_root_.MIPStarRE.QPBT.directDLineDescOf]
    simp [_root_.MIPStarRE.QPBT.lineRepMap_add_smul]
