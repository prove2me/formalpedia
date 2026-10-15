-- Prove2me | solution 1 for OAI.Paper092.signChange_measurePreserving
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T21:32:46.600291+00:00
-- url     : https://prove2.me/submissions/ddaf67db-15d8-452f-95cf-af6b0eb6a34d

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionVolume/SimplexVolume.lean:L42-L55
-- (upload_full_project.md Phase 4): solution for node OAI.Paper092.signChange_measurePreserving. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_ProjectionVolume
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexGeometry
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexProjection
import Definitions.Def_OAI_Geometry_ProjectionVolume_ProductProjection
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexNormals
import Definitions.Def_OAI_Geometry_ProjectionVolume_ProductNormals
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexVolume

-- ---- from OAI.Geometry.ProjectionVolume.SimplexVolume ----
namespace OAI

noncomputable section

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace Paper092

theorem signChange_measurePreserving {n : ℕ} (s : Fin n → Bool) :
    MeasurePreserving (signChange s) volume volume := by
  change MeasurePreserving (fun (x : Fin n → ℝ) i => if s i then x i else -x i) volume volume
  apply volume_preserving_pi (f := fun i (x : ℝ) => if s i then x else -x)
  intro i
  cases hs : s i
  · simpa only [hs, Bool.false_eq_true, ↓reduceIte] using
      (Measure.measurePreserving_neg (volume : Measure ℝ))
  · simp only [↓reduceIte]
    constructor
    · fun_prop
    · ext a ha
      rw [Measure.map_apply (by fun_prop) ha]
      rfl

end Paper092

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper092
open Set MeasureTheory
open scoped BigOperators ENNReal

theorem solution {n : ℕ} (s : Fin n → Bool) :
    MeasurePreserving (signChange s) volume volume := by
  first
    | exact OAI.Paper092.signChange_measurePreserving s
    | exact OAI.Paper092.signChange_measurePreserving
    | (apply OAI.Paper092.signChange_measurePreserving <;> assumption)
    | (intros; apply OAI.Paper092.signChange_measurePreserving <;> assumption)
