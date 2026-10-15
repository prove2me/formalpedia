-- Prove2me | solution 1 for OAI.RuledApproximation.coneTriangle_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T08:47:06.089391+00:00
-- url     : https://prove2.me/submissions/f705d30d-e00f-46c5-b39b-a3639ffe41dc

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/ConeVolume.lean:L16-L27
-- (upload_full_project.md Phase 4): solution for node OAI.RuledApproximation.coneTriangle_isCompact. The node keeps its source
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
import Definitions.Def_OAI_Geometry_RuledCovering_ConeVolume

-- ---- from OAI.Geometry.RuledCovering.SingularBounds ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma plane_norm_sq (z : Plane) : ‖z‖^2 = z 0^2+z 1^2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg ‖z i‖))]
  simp [Fin.sum_univ_succ,Real.norm_eq_abs]

lemma plane_norm_le_sum (z : Plane) : ‖z‖ ≤ |z 0|+|z 1| := by
  have h := plane_norm_sq z
  have h0 := abs_nonneg (z 0)
  have h1 := abs_nonneg (z 1)
  nlinarith [sq_abs (z 0),sq_abs (z 1)]

end RuledApproximation

end

end OAI

-- ---- from OAI.Geometry.RuledCovering.ConeVolume ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma coneTriangle_isCompact (a : ℝ) : IsCompact (coneTriangle a) := by
  have hc : IsClosed (coneTriangle a) := by
    unfold coneTriangle
    exact (isClosed_le (f := fun _ : Plane => (0:ℝ)) (g := fun z => z 1) (by fun_prop) (by fun_prop)).inter
      ((isClosed_le (f := fun z : Plane => z 1) (g := fun _ => a) (by fun_prop) (by fun_prop)).inter
        (isClosed_le (f := fun z : Plane => |z 0|) (g := fun z => z 1) (by fun_prop) (by fun_prop)))
  exact (isCompact_closedBall (0:Plane) (2*a)).of_isClosed_subset hc (by
    intro z hz
    rw [Metric.mem_closedBall,dist_zero_right]
    have he := plane_norm_le_sum z
    rw [abs_of_nonneg hz.1] at he
    exact he.trans (by linarith [hz.2.1,hz.2.2]))

end RuledApproximation

end

end OAI

-- ---- platform node ----
open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff


theorem solution : type_of% @_root_.OAI.RuledApproximation.coneTriangle_isCompact := @_root_.OAI.RuledApproximation.coneTriangle_isCompact
