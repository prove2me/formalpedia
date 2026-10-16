-- Prove2me | solution 1 for OAI.Solenoidal.zero_classical_solution
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T01:58:10.831023+00:00
-- url     : https://prove2.me/submissions/27a21ad3-14c2-4aa5-b20d-b2e897b7683a

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/SheetFlows/DirectForce.lean:L94-L126
-- (upload_full_project.md Phase 4): solution for node OAI.Solenoidal.zero_classical_solution. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SolenoidalSheetPrograms
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_DirectForce

-- ---- from OAI.MathematicalPhysics.SheetFlows.DirectForce ----
namespace OAI

/-! SheetFlows direct force. -/

section
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal

theorem zero_spatially_periodic : SpatiallyPeriodic (0 : Field) := by
  intro t x k
  rfl

theorem zero_divergence_free : DivergenceFree (0 : Field) := by
  intro t x
  simp [divergence]

theorem zero_classical_solution (ν : ℝ) :
    ClassicalSolution ν (0 : Field) 0 (0 : Pressure) where
  spatial_periodic_u := zero_spatially_periodic
  spatial_periodic_p := by intro t x k; rfl
  continuous_u := fun _ _ => continuous_const.continuousOn
  differentiable_t := fun _ _ _ => differentiableWithinAt_const _
  continuous_t := by
    intro T _
    rw [timePartial_zero]
    exact continuous_const.continuousOn
  differentiable_x := fun _ _ => differentiable_const _
  continuous_x := by
    intro T _ j
    simp only [spatialPartial_zero]
    exact continuous_const.continuousOn
  differentiable_xx := by
    intro t _ j
    rw [spatialPartial_zero]
    exact differentiable_const _
  continuous_xx := by
    intro T _ i j
    simp only [spatialPartial_zero]
    exact continuous_const.continuousOn
  continuous_p := fun _ _ => continuous_const.continuousOn
  differentiable_p := fun _ _ => differentiable_const _
  continuous_px := by
    intro T _
    rw [gradient_zero]
    exact continuous_const.continuousOn
  pressure_mean_zero := by intro t _; simp
  incompressible := fun t _ x => zero_divergence_free t x
  initial := fun _ => rfl
  equation := by intro t _ x; simp

end Solenoidal
end
end

end OAI

-- ---- platform node ----
open OAI OAI.Solenoidal
open Set MeasureTheory
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Solenoidal.zero_classical_solution := @_root_.OAI.Solenoidal.zero_classical_solution
