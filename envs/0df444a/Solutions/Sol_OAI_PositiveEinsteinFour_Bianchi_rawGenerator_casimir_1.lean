-- Prove2me | solution 1 for OAI.PositiveEinsteinFour.Bianchi.rawGenerator_casimir_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T19:18:19.80504+00:00
-- url     : https://prove2.me/submissions/d5cd1dc0-b463-4597-90f7-3b62671dd9f2

import Mathlib
import Definitions.Def_OAIQ091C007

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GradientOperator
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Bianchi.derivativeQuaternion_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawNorm_matrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual generator commutators on the Bianchi gradient coordinates. -/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators
open TraceHessian

private theorem rawGenerator_casimir_1_0 (Z : Tensor)
    (_hz : Z.traceFree) (hb : Z.bianchi) :
    (∑ s : Fin 3, rawGradientGenerator s (rawGradientGenerator s Z.matrix) 1 0) =
      (-35 : ℝ) • Z.matrix 1 0 := by
  ext u
  have hc := congrArg (fun v : Vec => v u) (gradientCoupling_eq Z hb 1 0)
  fin_cases u <;>
    simp [rawGradientGenerator, rawMatrixRotation, gradientCoupling,
      matrixRotation, TraceHessian.rotation, quaternion, Tensor.matrix,
      Fin.sum_univ_succ] at hc ⊢
  all_goals linear_combination 2 * hc

private theorem rawGenerator_casimir_1_1 (Z : Tensor)
    (hz : Z.traceFree) (hb : Z.bianchi) :
    (∑ s : Fin 3, rawGradientGenerator s (rawGradientGenerator s Z.matrix) 1 1) =
      (-35 : ℝ) • Z.matrix 1 1 := by
  ext u
  have hc := congrArg (fun v : Vec => v u) (gradientCoupling_eq Z hb 1 1)
  have ht := congrArg (fun v : Vec => v u) hz
  fin_cases u <;>
    simp [rawGradientGenerator, rawMatrixRotation, gradientCoupling,
      matrixRotation, TraceHessian.rotation, quaternion, Tensor.matrix,
      Fin.sum_univ_succ] at hc ht ⊢
  all_goals first | linear_combination 2 * hc | linear_combination 2 * hc + 8 * ht

private theorem rawGenerator_casimir_1_2 (Z : Tensor)
    (_hz : Z.traceFree) (hb : Z.bianchi) :
    (∑ s : Fin 3, rawGradientGenerator s (rawGradientGenerator s Z.matrix) 1 2) =
      (-35 : ℝ) • Z.matrix 1 2 := by
  ext u
  have hc := congrArg (fun v : Vec => v u) (gradientCoupling_eq Z hb 1 2)
  fin_cases u <;>
    simp [rawGradientGenerator, rawMatrixRotation, gradientCoupling,
      matrixRotation, TraceHessian.rotation, quaternion, Tensor.matrix,
      Fin.sum_univ_succ] at hc ⊢
  all_goals linear_combination 2 * hc

private theorem rawGenerator_casimir_1_oai (Z : Tensor)
    (hz : Z.traceFree) (hb : Z.bianchi) (b : Fin 3) :
    (∑ s : Fin 3, rawGradientGenerator s (rawGradientGenerator s Z.matrix) 1 b) =
      (-35 : ℝ) • Z.matrix 1 b := by
  fin_cases b
  · exact rawGenerator_casimir_1_0 Z hz hb
  · exact rawGenerator_casimir_1_1 Z hz hb
  · exact rawGenerator_casimir_1_2 Z hz hb

end
end PositiveEinsteinFour.Bianchi

end OAI
end

theorem solution : type_of% @OAI.PositiveEinsteinFour.Bianchi.rawGenerator_casimir_1_oai := @OAI.PositiveEinsteinFour.Bianchi.rawGenerator_casimir_1_oai
