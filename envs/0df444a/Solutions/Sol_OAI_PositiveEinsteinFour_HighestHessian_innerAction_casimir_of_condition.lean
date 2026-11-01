-- Prove2me | solution 1 for OAI.PositiveEinsteinFour.HighestHessian.innerAction_casimir_of_condition
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T19:47:00.279704+00:00
-- url     : https://prove2.me/submissions/3944256a-c037-4528-a278-c8336e4bef80

import Mathlib
import Definitions.Def_OAIQ091C018
import Theorems.Thm_OAI_PositiveEinsteinFour_Bianchi_rawGenerator_casimir_1
import Theorems.Thm_OAI_PositiveEinsteinFour_Bianchi_rawGenerator_casimir_2

section
-- module Solutions.OAIQ091_EF.EinsteinFour_BianchiSlices
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Bianchi.derivativeQuaternion_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawGradientGenerator_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawMatrixRotation_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawNorm_matrix _root_.OAI.PositiveEinsteinFour.HighestHessian.coupledOperator_coordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual gradient slices of a four-slot Hessian. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

theorem innerSlice_traceFree (X : Hessian) (i : Fin 4)
    (ht : ∀ j, traceFree (X i j)) : (innerSlice X i).traceFree := by
  ext j
  simpa [Tensor.traceFree, innerSlice, traceFree, Fin.sum_univ_three] using ht j

/-- The concrete highest-Hessian constraints give genuine Bianchi slices. -/
theorem innerSlice_of_condition (X : Hessian) (hX : condition X) (i : Fin 4) :
    (innerSlice X i).traceFree ∧ (innerSlice X i).bianchi := by
  exact ⟨innerSlice_traceFree X i (fun j => (hX.2.1 i j).2),
    innerSlice_bianchi X i (fun j => (hX.2.1 i j).1) (hX.2.2.2 i)⟩

end
end PositiveEinsteinFour.HighestHessian

end OAI
end

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

private theorem rawGenerator_casimir_0_0 (Z : Tensor)
    (hz : Z.traceFree) (hb : Z.bianchi) :
    (∑ s : Fin 3, rawGradientGenerator s (rawGradientGenerator s Z.matrix) 0 0) =
      (-35 : ℝ) • Z.matrix 0 0 := by
  ext u
  have hc := congrArg (fun v : Vec => v u) (gradientCoupling_eq Z hb 0 0)
  have ht := congrArg (fun v : Vec => v u) hz
  fin_cases u <;>
    simp [rawGradientGenerator, rawMatrixRotation, gradientCoupling,
      matrixRotation, TraceHessian.rotation, quaternion, Tensor.matrix,
      Fin.sum_univ_succ] at hc ht ⊢
  all_goals first | linear_combination 2 * hc | linear_combination 2 * hc + 8 * ht

private theorem rawGenerator_casimir_0_1 (Z : Tensor)
    (_hz : Z.traceFree) (hb : Z.bianchi) :
    (∑ s : Fin 3, rawGradientGenerator s (rawGradientGenerator s Z.matrix) 0 1) =
      (-35 : ℝ) • Z.matrix 0 1 := by
  ext u
  have hc := congrArg (fun v : Vec => v u) (gradientCoupling_eq Z hb 0 1)
  fin_cases u <;>
    simp [rawGradientGenerator, rawMatrixRotation, gradientCoupling,
      matrixRotation, TraceHessian.rotation, quaternion, Tensor.matrix,
      Fin.sum_univ_succ] at hc ⊢
  all_goals linear_combination 2 * hc

private theorem rawGenerator_casimir_0_2 (Z : Tensor)
    (_hz : Z.traceFree) (hb : Z.bianchi) :
    (∑ s : Fin 3, rawGradientGenerator s (rawGradientGenerator s Z.matrix) 0 2) =
      (-35 : ℝ) • Z.matrix 0 2 := by
  ext u
  have hc := congrArg (fun v : Vec => v u) (gradientCoupling_eq Z hb 0 2)
  fin_cases u <;>
    simp [rawGradientGenerator, rawMatrixRotation, gradientCoupling,
      matrixRotation, TraceHessian.rotation, quaternion, Tensor.matrix,
      Fin.sum_univ_succ] at hc ⊢
  all_goals linear_combination 2 * hc

private theorem rawGenerator_casimir_0 (Z : Tensor)
    (hz : Z.traceFree) (hb : Z.bianchi) (b : Fin 3) :
    (∑ s : Fin 3, rawGradientGenerator s (rawGradientGenerator s Z.matrix) 0 b) =
      (-35 : ℝ) • Z.matrix 0 b := by
  fin_cases b
  · exact rawGenerator_casimir_0_0 Z hz hb
  · exact rawGenerator_casimir_0_1 Z hz hb
  · exact rawGenerator_casimir_0_2 Z hz hb

/-- The pointwise Casimir identity follows from the actual trace and Bianchi equations. -/
theorem rawGradientGenerator_casimir (Z : Tensor) (hz : Z.traceFree) (hb : Z.bianchi)
    (a b : Fin 3) :
    (∑ s : Fin 3, rawGradientGenerator s (rawGradientGenerator s Z.matrix) a b) =
      (-35 : ℝ) • Z.matrix a b := by
  fin_cases a
  · exact rawGenerator_casimir_0 Z hz hb b
  · exact rawGenerator_casimir_1 Z hz hb b
  · exact rawGenerator_casimir_2 Z hz hb b

end
end PositiveEinsteinFour.Bianchi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CoupledCasimir
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Bianchi.derivativeQuaternion_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawNorm_matrix _root_.OAI.PositiveEinsteinFour.Geometry.matrixSlot_apply _root_.OAI.PositiveEinsteinFour.QuaternionFrame.fieldRaw_rawField _root_.OAI.PositiveEinsteinFour.QuaternionFrame.frameMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The plus spectral polynomial on the actual highest-Hessian space. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

theorem innerAction_rawSlice (s : Fin 3) (X : Hessian) (i : Fin 4) :
    rawSlice (innerAction s X) i = rawGradientGenerator s (rawSlice X i) := by
  funext b c
  ext j
  have h := quaternionMatrix_apply s (rawSlice X i b c) j
  simp only [rawSlice, Fin.sum_univ_four] at h
  simp [rawSlice, innerAction, rawGradientGenerator, rawMatrixRotation,
    matrixAction, Fin.sum_univ_three, Fin.sum_univ_four]
  rw [← h]
  ring

/-- The inner Casimir acts on the actual Bianchi slices. -/
theorem innerAction_casimir_of_condition_oai (X : Hessian) (hX : condition X) :
    (∑ s : Fin 3, innerAction s (innerAction s X)) = (-35 : ℝ) • X := by
  funext i j b c
  simp only [Fin.sum_univ_three, Pi.add_apply, Matrix.add_apply]
  obtain ⟨hz, hb⟩ := innerSlice_of_condition X hX i
  have hr : rawSlice X i = (innerSlice X i).matrix := by
    funext a b
    exact (innerSlice_matrix X i (fun j => (hX.2.1 i j).1) a b).symm
  have hh := rawGradientGenerator_casimir (innerSlice X i) hz hb b c
  have h := congrArg (fun v : Vec => v j) hh
  have hs (s : Fin 3) : innerAction s (innerAction s X) i j b c =
      rawGradientGenerator s (rawGradientGenerator s (innerSlice X i).matrix) b c j := by
    change rawSlice (innerAction s (innerAction s X)) i b c j = _
    rw [innerAction_rawSlice, innerAction_rawSlice, hr]
  simp only [Fin.sum_univ_three] at h ⊢
  simp only [hs]
  simpa [← hr, rawSlice] using h

end
end PositiveEinsteinFour.HighestHessian

end OAI
end

theorem solution : type_of% @OAI.PositiveEinsteinFour.HighestHessian.innerAction_casimir_of_condition_oai := @OAI.PositiveEinsteinFour.HighestHessian.innerAction_casimir_of_condition_oai
