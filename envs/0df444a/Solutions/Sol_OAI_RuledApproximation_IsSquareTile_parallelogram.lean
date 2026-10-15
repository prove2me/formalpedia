-- Prove2me | solution 1 for OAI.RuledApproximation.IsSquareTile.parallelogram
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T08:18:03.630378+00:00
-- url     : https://prove2.me/submissions/51e1234f-faa1-45f4-8f18-7e1c26690dc8

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/SquareCover.lean:L192-L204
-- (upload_full_project.md Phase 4): solution for node OAI.RuledApproximation.IsSquareTile.parallelogram. The node keeps its source
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
import Theorems.Thm_OAI_RuledApproximation_IsParallelogram_linear_image
import Theorems.Thm_OAI_RuledApproximation_coordinates_closedBall_parallelogram

-- ---- from OAI.Geometry.RuledCovering.Isometries ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma IsParallelogram.translate {E : Type*} [AddCommGroup E] [Module ℝ E]
    {P : Set E} (hP : IsParallelogram P) (a : E) :
    IsParallelogram ((fun x => a + x) '' P) := by
  obtain ⟨c, u, v, hli, rfl⟩ := hP
  refine ⟨a+c, u, v, hli, ?_⟩
  ext x
  constructor
  · rintro ⟨_, ⟨s, hs, t, ht, rfl⟩, rfl⟩
    exact ⟨s, hs, t, ht, by abel_nf⟩
  · rintro ⟨s, hs, t, ht, rfl⟩
    exact ⟨c+s•u+t•v, ⟨s, hs, t, ht, rfl⟩, by abel_nf⟩

end RuledApproximation

end

end OAI

-- ---- from OAI.Geometry.RuledCovering.SquareCover ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma unitSquare_parallelogram : IsParallelogram unitSquare := by
  have he : unitSquare = (EuclideanSpace.equiv (Fin 2) ℝ).symm ''
      closedBall (0 : Coordinates) (1/2:ℝ) := by
    ext x
    constructor
    · intro hx
      refine ⟨WithLp.ofLp x, ?_, rfl⟩
      rw [mem_closedBall,dist_zero_right,pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1/2)]
      exact hx
    · rintro ⟨y,hy,rfl⟩
      rw [mem_closedBall,dist_zero_right,pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1/2)] at hy
      exact hy
  rw [he]
  exact (coordinates_closedBall_parallelogram 0 (by norm_num : (0:ℝ)<1/2)).linear_image
    (EuclideanSpace.equiv (Fin 2) ℝ).symm.toLinearMap
    (EuclideanSpace.equiv (Fin 2) ℝ).symm.injective

lemma IsSquareTile.parallelogram {T : Set Plane} (hT : IsSquareTile T) :
    IsParallelogram T := by
  obtain ⟨c,R,a,ha,rfl⟩ := hT
  have hi : Function.Injective (a • R.toLinearMap) := by
    intro x y hxy
    apply R.injective
    exact (smul_right_injective Plane ha.ne') hxy
  have he : (fun x => c+a • R x) '' unitSquare =
      (fun x => c+x) '' ((a • R.toLinearMap) '' unitSquare) := by
    rw [← image_comp]
    rfl
  rw [he]
  exact (unitSquare_parallelogram.linear_image (a • R.toLinearMap) hi).translate c

end RuledApproximation

end

end OAI

-- ---- platform node ----
open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff


theorem solution : type_of% @_root_.OAI.RuledApproximation.IsSquareTile.parallelogram := @_root_.OAI.RuledApproximation.IsSquareTile.parallelogram
