-- Prove2me | solution 1 for OAI.RuledApproximation.projectedCylinder_carrier
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T07:26:56.974462+00:00
-- url     : https://prove2.me/submissions/e2b06aa2-613e-4aa7-b609-f75fce9e6434

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/Projection.lean:L221-L235
-- (upload_full_project.md Phase 4): solution for node OAI.RuledApproximation.projectedCylinder_carrier. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Theorems.Thm_OAI_RuledApproximation_projectedCylinder_mem_iff

-- ---- from OAI.Geometry.RuledCovering.Projection ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma projectedCylinder_carrier (h : ℝ) (g : Plane) (P : Set Plane) :
    (projectedCylinder h g P).carrier = firstPhysicalMap h '' auxiliaryCylinder P g := by
  ext x
  rw [projectedCylinder_mem_iff]
  constructor
  · rintro ⟨p, hp, s, rfl⟩
    refine ⟨axial s (p + s • g), ⟨s, p, hp, rfl⟩, ?_⟩
    ext i
    fin_cases i <;> simp [firstPhysicalMap, axial, vec3, planeEmbedding, physicalDirection,
      mul_add, mul_left_comm]
  · rintro ⟨_, ⟨s, p, hp, rfl⟩, rfl⟩
    refine ⟨p, hp, s, ?_⟩
    ext i
    fin_cases i <;> simp [firstPhysicalMap, axial, vec3, planeEmbedding, physicalDirection,
      mul_add, mul_left_comm]

end RuledApproximation

end

end OAI

-- ---- platform node ----
open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff


theorem solution : type_of% @_root_.OAI.RuledApproximation.projectedCylinder_carrier := @_root_.OAI.RuledApproximation.projectedCylinder_carrier
