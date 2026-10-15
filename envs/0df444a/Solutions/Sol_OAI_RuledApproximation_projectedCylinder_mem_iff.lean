-- Prove2me | solution 1 for OAI.RuledApproximation.projectedCylinder_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T07:25:45.830981+00:00
-- url     : https://prove2.me/submissions/952ee6a6-2f51-42ca-9e9e-1f6806c7f191

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/Projection.lean:L195-L219
-- (upload_full_project.md Phase 4): solution for node OAI.RuledApproximation.projectedCylinder_mem_iff. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection

-- ---- from OAI.Geometry.RuledCovering.Projection ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma projectedCylinder_mem_iff (h : ℝ) (g : Plane) (P : Set Plane) (x : Space) :
    x ∈ (projectedCylinder h g P).carrier ↔
      ∃ p ∈ P, ∃ s : ℝ, x = planeEmbedding h p + s • physicalDirection h g := by
  have hid (p : Plane) (t : ℝ) :
      (perpendicularProjection h g p : Space) + t • physicalUnit h g =
        planeEmbedding h p +
          (t / ‖physicalDirection h g‖ -
            inner ℝ (physicalDirection h g) (planeEmbedding h p) /
              ‖physicalDirection h g‖ ^ 2) • physicalDirection h g := by
    change (planeEmbedding h p -
      (inner ℝ (physicalDirection h g) (planeEmbedding h p) /
        ‖physicalDirection h g‖ ^ 2) • physicalDirection h g) +
      t • (‖physicalDirection h g‖⁻¹ • physicalDirection h g) = _
    simp only [div_eq_mul_inv, smul_smul]
    module
  constructor
  · rintro ⟨q, ⟨p, hp, rfl⟩, t, rfl⟩
    exact ⟨p, hp, _, hid p t⟩
  · rintro ⟨p, hp, s, rfl⟩
    refine ⟨perpendicularProjection h g p, ⟨p, hp, rfl⟩,
      (s + inner ℝ (physicalDirection h g) (planeEmbedding h p) /
        ‖physicalDirection h g‖ ^ 2) * ‖physicalDirection h g‖, ?_⟩
    change planeEmbedding h p + s • physicalDirection h g =
      (perpendicularProjection h g p : Space) + _ • physicalUnit h g
    rw [hid, mul_div_cancel_right₀ _ (physicalDirection_norm_pos h g).ne', add_sub_cancel_right]

end RuledApproximation

end

end OAI

-- ---- platform node ----
open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff


theorem solution : type_of% @_root_.OAI.RuledApproximation.projectedCylinder_mem_iff := @_root_.OAI.RuledApproximation.projectedCylinder_mem_iff
