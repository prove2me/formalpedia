-- Prove2me | solution 1 for OAI.PositiveEinsteinFour.HighestHessian.highestProjection_condition
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T19:45:06.484274+00:00
-- url     : https://prove2.me/submissions/3cb96e2d-48e0-47c0-9623-c7736574517f

import Mathlib
import Definitions.Def_OAIQ091C015

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HighestCondition
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Bianchi.derivativeQuaternion_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawGradientGenerator_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawMatrixRotation_matrix _root_.OAI.PositiveEinsteinFour.Geometry.matrixSlot_apply _root_.OAI.PositiveEinsteinFour.QuaternionFrame.frameMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The displayed highest coordinates satisfy every original tensor constraint. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

/-- Symmetry is built into the two derivative slots of the coordinate array. -/
theorem highest_derivative_symmetric (c : Fin 21 → ℝ) (i j : Fin 4) :
    highest c i j = highest c j i := by
  fin_cases i <;> fin_cases j <;> rfl

theorem highest_matrix_symmetric (c : Fin 21 → ℝ) (i j : Fin 4) :
    symmetric (highest c i j) := by
  intro a b
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [ofCoordinates]

theorem highest_matrix_traceFree (c : Fin 21 → ℝ) (i j : Fin 4) :
    traceFree (highest c i j) := by
  fin_cases i <;> fin_cases j <;>
    simp [traceFree, ofCoordinates, Fin.sum_univ_succ]
  all_goals ring

theorem highest_trace (c : Fin 21 → ℝ) : hessianTrace (highest c) = 0 := by
  ext a b
  change (∑ i, highest c i i a b) = 0
  fin_cases a <;> fin_cases b <;>
    simp [ofCoordinates, Fin.sum_univ_succ]
  all_goals ring

theorem highest_divergence (c : Fin 21 → ℝ) (i : Fin 4) (r : Fin 3) :
    divergence (highest c) i r = 0 := by
  ext u
  fin_cases i <;> fin_cases r <;> fin_cases u <;>
    simp [divergence, quaternion, Fin.sum_univ_succ]
  all_goals simp [ofCoordinates]
  all_goals ring

/-- The concrete constrained-space description in both directions. -/
theorem highest_condition (c : Fin 21 → ℝ) : condition (highest c) := by
  refine ⟨highest_derivative_symmetric c, ?_, highest_trace c, highest_divergence c⟩
  intro i j
  exact ⟨highest_matrix_symmetric c i j, highest_matrix_traceFree c i j⟩

end
end PositiveEinsteinFour.HighestHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HighestProjection
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The orthogonal projection is constructed from the actual tensor subspace. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

theorem hessianVector_injective : Function.Injective hessianVector := by
  intro X Y h
  simpa only [vectorHessian_hessianVector] using congrArg vectorHessian h

theorem highestProjection_has_coordinates (X : Hessian) :
    ∃ c : Fin 21 → ℝ, highest c = highestProjection X := by
  have h := highestSubspace.starProjection_apply_mem (hessianVector X)
  obtain ⟨c, hc⟩ := h
  refine ⟨c, hessianVector_injective ?_⟩
  change hessianVector (highest c) =
    highestSubspace.starProjection (hessianVector X) at hc
  simpa only [highestProjection, hessianVector_vectorHessian] using hc

theorem highestProjection_condition_oai (X : Hessian) : condition (highestProjection X) := by
  obtain ⟨c, hc⟩ := highestProjection_has_coordinates X
  rw [← hc]
  exact highest_condition c

end
end PositiveEinsteinFour.HighestHessian

end OAI
end

theorem solution : type_of% @OAI.PositiveEinsteinFour.HighestHessian.highestProjection_condition_oai := @OAI.PositiveEinsteinFour.HighestHessian.highestProjection_condition_oai
