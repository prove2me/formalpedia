-- Prove2me | solution 1 for OAI.RuledApproximation.frame_integral_image
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T07:28:13.543279+00:00
-- url     : https://prove2.me/submissions/5fb9416d-6e5c-4df4-8358-a8eba0c746d0

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/Frames.lean:L21-L36
-- (upload_full_project.md Phase 4): solution for node OAI.RuledApproximation.frame_integral_image. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames

-- ---- from OAI.Geometry.RuledCovering.Frames ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma frame_integral_image (M : Coordinates ≃L[ℝ] Plane) {K : Set Coordinates}
    (hK : MeasurableSet K) (F : Plane → ℝ) :
    (∫ p in M '' K, F p) = frameJacobian M * (∫ x in K, F (M x)) := by
  let e := EuclideanSpace.equiv (Fin 2) ℝ
  let D := M.trans e
  have himage : M '' K = e.symm '' (D '' K) := by
    rw [← image_comp]
    congr 1

  rw [himage]
  have hmp : MeasurePreserving e.symm volume volume := PiLp.volume_preserving_toLp (Fin 2)
  rw [hmp.setIntegral_image_emb e.symm.toHomeomorph.measurableEmbedding]
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hK
    (fun x _ => D.hasFDerivAt.hasFDerivWithinAt) D.injective.injOn]
  rw [integral_smul]
  rfl

end RuledApproximation

end

end OAI

-- ---- platform node ----
open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff


theorem solution : type_of% @_root_.OAI.RuledApproximation.frame_integral_image := @_root_.OAI.RuledApproximation.frame_integral_image
