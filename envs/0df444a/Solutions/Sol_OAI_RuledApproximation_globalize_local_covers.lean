-- Prove2me | solution 1 for OAI.RuledApproximation.globalize_local_covers
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T07:53:52.275413+00:00
-- url     : https://prove2.me/submissions/4d1de05f-dc6f-49f0-9661-103318ebc0ba

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/HyperbolicCover.lean:L253-L278
-- (upload_full_project.md Phase 4): solution for node OAI.RuledApproximation.globalize_local_covers. The node keeps its source
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
import Theorems.Thm_OAI_RuledApproximation_glue_finite_local_covers

-- ---- from OAI.Geometry.RuledCovering.HyperbolicCover ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

/-- Compactness and null-frontier patches globalize the finite local producer. -/
theorem globalize_local_covers {shape : Cylinder → Prop} (h L : ℝ) (v : Plane → Plane)
    (F : Plane → ℝ) (A : ℝ) {K : Set Plane} (hK : IsCompact K) (hF : IntegrableOn F K)
    (hpatch : ∀ p ∈ K, ∃ V : Set Plane, IsOpen V ∧ p ∈ V ∧
      ∀ Q : Set Plane, IsCompact Q → Q ⊆ V → ∀ eps : ℝ, 0 < eps →
      HasFiniteCover shape (physicalRuled h Q v L) (A * (∫ q in Q, F q) + eps))
    {eps : ℝ} (heps : 0 < eps) :
    HasFiniteCover shape (physicalRuled h K v L) (A * (∫ q in K, F q) + eps) := by
  classical
  choose V hVo hpV hloc using fun p : K => hpatch p p.property
  choose r hr hrV using fun p : K => Metric.mem_nhds_iff.mp ((hVo p).mem_nhds (hpV p))
  let O : K → Set Plane := fun p => ball (p : Plane) (r p / 2)
  have hOo : ∀ p : K, IsOpen (O p) := fun _ => isOpen_ball
  have hcover : K ⊆ ⋃ p : K, O p := by
    intro p hp
    exact mem_iUnion.mpr ⟨⟨p, hp⟩, mem_ball_self (half_pos (hr ⟨p, hp⟩))⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover O hOo hcover
  apply glue_finite_local_covers h L v F s O V (fun p _ => hOo p) _ _
    (fun p _ => hloc p) hK hF hs heps
  · intro p _
    rw [show O p = ball (p : Plane) (r p / 2) from rfl,
      closure_ball (p : Plane) (half_pos (hr p)).ne']
    exact (closedBall_subset_ball (by linarith [hr p])).trans (hrV p)
  · intro p _
    apply measure_mono_null frontier_ball_subset_sphere
    exact MeasureTheory.Measure.addHaar_sphere volume (p : Plane) (r p / 2)

end RuledApproximation

end

end OAI

-- ---- platform node ----
open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff


theorem solution : type_of% @_root_.OAI.RuledApproximation.globalize_local_covers := @_root_.OAI.RuledApproximation.globalize_local_covers
