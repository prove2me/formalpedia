-- Prove2me | solution 1 for OAI.RuledApproximation.singular_tip_small
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T08:32:43.991203+00:00
-- url     : https://prove2.me/submissions/e04293ca-8c23-4e6b-9fb5-2d0364eb8401

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/SingularBounds.lean:L102-L116
-- (upload_full_project.md Phase 4): solution for node OAI.RuledApproximation.singular_tip_small. The node keeps its source
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

-- ---- from OAI.Geometry.RuledCovering.SingularBounds ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma singular_tip_small {gamma : ℝ} (hg : 1 < gamma) :
    Asymptotics.IsLittleO (𝓝[>] (0:ℝ)) (fun c : ℝ => (c^gamma)^2) (fun c => c^2) := by
  rw [Asymptotics.isLittleO_iff_tendsto']
  · have h : Tendsto (fun c : ℝ => c^(2*gamma-2)) (𝓝[>] 0)
        (𝓝 ((0:ℝ)^(2*gamma-2))) :=
      ((Real.continuous_rpow_const (show 0 ≤ 2*gamma-2 by linarith)).tendsto 0).mono_left nhdsWithin_le_nhds
    rw [Real.zero_rpow (by linarith : 2*gamma-2 ≠ 0)] at h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with c hc
    have hc : 0 < c := hc
    rw [← Real.rpow_natCast,← Real.rpow_mul hc.le,← Real.rpow_natCast,← Real.rpow_sub hc]
    congr 1
    ring
  · filter_upwards [self_mem_nhdsWithin] with c hc
    exact fun h => False.elim ((ne_of_gt (pow_pos hc 2)) h)

end RuledApproximation

end

end OAI

-- ---- platform node ----
open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff


theorem solution : type_of% @_root_.OAI.RuledApproximation.singular_tip_small := @_root_.OAI.RuledApproximation.singular_tip_small
