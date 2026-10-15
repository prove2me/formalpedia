-- Prove2me | solution 1 for OAI.RuledApproximation.c1_local_remainder
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T07:40:54.317675+00:00
-- url     : https://prove2.me/submissions/cca2996e-ab20-4bfb-920b-09aa8a286aaa

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/LocalApproximation.lean:L13-L31
-- (upload_full_project.md Phase 4): solution for node OAI.RuledApproximation.c1_local_remainder. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames
import Definitions.Def_OAI_Geometry_RuledCovering_OuterApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_Lattice
import Definitions.Def_OAI_Geometry_RuledCovering_LocalApproximation

-- ---- from OAI.Geometry.RuledCovering.LocalApproximation ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

/-- A quantitative derivative remainder in convex local coordinates. -/
theorem c1_local_remainder {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {v : E → F} {U : Set E} (hU : IsOpen U) (hv : ContDiffOn ℝ 1 v U)
    {p : E} (hp : p ∈ U) {delta : ℝ} (hd : 0 < delta) :
    ∃ r : ℝ, 0 < r ∧ ball p r ⊆ U ∧ ∀ x ∈ ball p r, ∀ y ∈ ball p r,
      ‖v x - v y - fderiv ℝ v p (x - y)‖ ≤ delta * ‖x - y‖ := by
  have hdc : ContinuousAt (fderiv ℝ v) p :=
    (hv.contDiffAt (hU.mem_nhds hp)).continuousAt_fderiv (by norm_num)
  have hevent : ∀ᶠ x in 𝓝 p, ‖fderiv ℝ v x - fderiv ℝ v p‖ < delta := by
    simpa only [dist_eq_norm] using hdc.eventually (ball_mem_nhds _ hd)
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hevent (hU.mem_nhds hp))
  have hsub : ball p r ⊆ U := fun x hx => (hrsub hx).2
  refine ⟨r, hr, hsub, ?_⟩
  intro x hx y hy
  apply (convex_ball p r).norm_image_sub_le_of_norm_hasFDerivWithin_le' (φ := fderiv ℝ v p)
    (fun z hz => ((hv.contDiffAt (hU.mem_nhds (hsub hz))).differentiableAt
      (by norm_num)).hasFDerivAt.hasFDerivWithinAt)
    (fun z hz => (hrsub hz).1.le) hy hx

end RuledApproximation

end

end OAI

-- ---- platform node ----
open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff


theorem solution : type_of% @_root_.OAI.RuledApproximation.c1_local_remainder := @_root_.OAI.RuledApproximation.c1_local_remainder
