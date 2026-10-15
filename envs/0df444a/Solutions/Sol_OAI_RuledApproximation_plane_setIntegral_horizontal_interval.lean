-- Prove2me | solution 1 for OAI.RuledApproximation.plane_setIntegral_horizontal_interval
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T08:45:03.955737+00:00
-- url     : https://prove2.me/submissions/b24c6a86-040a-4341-b22e-f386fc81a7e9

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/PlanarIntegration.lean:L70-L88
-- (upload_full_project.md Phase 4): solution for node OAI.RuledApproximation.plane_setIntegral_horizontal_interval. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames
import Definitions.Def_OAI_Geometry_RuledCovering_OuterApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_Lattice
import Definitions.Def_OAI_Geometry_RuledCovering_LocalApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicLattice
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicCover
import Definitions.Def_OAI_Geometry_RuledCovering_Isometries
import Definitions.Def_OAI_Geometry_RuledCovering_Hyperbolic
import Definitions.Def_OAI_Geometry_RuledCovering_NilpotentLattice
import Definitions.Def_OAI_Geometry_RuledCovering_Nilpotent
import Definitions.Def_OAI_Geometry_RuledCovering_SingularField
import Definitions.Def_OAI_Geometry_RuledCovering_PlanarIntegration

-- ---- from OAI.Geometry.RuledCovering.PlanarIntegration ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma pairPlane_measurePreserving : MeasurePreserving pairPlaneEquiv volume volume :=
  (PiLp.volume_preserving_toLp (Fin 2)).comp (volume_preserving_finTwoArrow ℝ).symm

lemma plane_integral_pair (f : Plane → ℝ) :
    (∫ z, f z) = ∫ q : ℝ × ℝ, f (vec2 q.1 q.2) :=
  (pairPlane_measurePreserving.integral_comp pairPlaneEquiv.measurableEmbedding f).symm

lemma plane_integrable_pair (f : Plane → ℝ) :
    Integrable (fun q : ℝ × ℝ => f (vec2 q.1 q.2)) ↔ Integrable f :=
  pairPlane_measurePreserving.integrable_comp_emb pairPlaneEquiv.measurableEmbedding

lemma plane_setIntegral_horizontal {S : Set Plane} (hS : MeasurableSet S)
    {f : Plane → ℝ} (hf : IntegrableOn f S) :
    (∫ z in S, f z) = ∫ r : ℝ, ∫ b in {b : ℝ | vec2 b r ∈ S}, f (vec2 b r) := by
  rw [← integral_indicator hS,plane_integral_pair]
  rw [Measure.volume_eq_prod,integral_prod_symm _ (by simpa only [Measure.volume_eq_prod] using (plane_integrable_pair _).mpr (hf.integrable_indicator hS))]
  apply integral_congr_ae
  filter_upwards with r
  have hm : MeasurableSet {b : ℝ | vec2 b r ∈ S} := hS.preimage (pairPlaneEquiv.measurable.comp (measurable_id.prodMk measurable_const))
  rw [← integral_indicator hm]
  rfl

lemma plane_setIntegral_horizontal_interval {S : Set Plane} (hS : MeasurableSet S)
    {f : Plane → ℝ} (hf : IntegrableOn f S) {s : Set ℝ} (hs : MeasurableSet s)
    {l u : ℝ → ℝ} (heq : ∀ z : Plane, z ∈ S ↔ z 1 ∈ s ∧ z 0 ∈ Icc (l (z 1)) (u (z 1))) :
    (∫ z in S, f z) = ∫ r in s, ∫ b in Icc (l r) (u r), f (vec2 b r) := by
  rw [plane_setIntegral_horizontal hS hf,← integral_indicator hs]
  congr 1
  funext r
  by_cases hr : r ∈ s
  · rw [Set.indicator_of_mem hr]
    apply setIntegral_congr_set
    filter_upwards with b
    apply propext
    change vec2 b r ∈ S ↔ b ∈ Icc (l r) (u r)
    simpa only [vec2_apply_zero,vec2_apply_one,hr,true_and] using heq (vec2 b r)
  · rw [Set.indicator_of_notMem hr]
    have he : {b : ℝ | vec2 b r ∈ S} = ∅ := by
      ext b
      simpa [hr] using heq (vec2 b r)
    simp [he]

end RuledApproximation

end

end OAI

-- ---- platform node ----
open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff


theorem solution : type_of% @_root_.OAI.RuledApproximation.plane_setIntegral_horizontal_interval := @_root_.OAI.RuledApproximation.plane_setIntegral_horizontal_interval
