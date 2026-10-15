-- Prove2me | solution 1 for OAI.RuledApproximation.IsParallelogram.linear_image
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T07:24:14.350981+00:00
-- url     : https://prove2.me/submissions/81ccaebb-384d-4930-aebf-db59a8037a05

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/Projection.lean:L161-L177
-- (upload_full_project.md Phase 4): solution for node OAI.RuledApproximation.IsParallelogram.linear_image. The node keeps its source
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

lemma IsParallelogram.linear_image {E F : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    {P : Set E} (hP : IsParallelogram P) (f : E →ₗ[ℝ] F) (hf : Function.Injective f) :
    IsParallelogram (f '' P) := by
  obtain ⟨c, u, v, hli, rfl⟩ := hP
  refine ⟨f c, f u, f v, ?_, ?_⟩
  · have hli' := hli.map' f (LinearMap.ker_eq_bot.mpr hf)
    have heq : (f ∘ ![u, v]) = ![f u, f v] := by
      funext i
      fin_cases i <;> rfl
    rwa [heq] at hli'
  · ext x
    constructor
    · rintro ⟨y, ⟨a, ha, b, hb, rfl⟩, rfl⟩
      exact ⟨a, ha, b, hb, by simp⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨c + a • u + b • v, ⟨a, ha, b, hb, rfl⟩, by simp⟩

end RuledApproximation

end

end OAI

-- ---- platform node ----
open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff


theorem solution : type_of% @_root_.OAI.RuledApproximation.IsParallelogram.linear_image := @_root_.OAI.RuledApproximation.IsParallelogram.linear_image
