-- Prove2me | solution 1 for OAI.Paper092.twice_sum_negative_eq_sum_abs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T21:31:33.847016+00:00
-- url     : https://prove2.me/submissions/95592aa6-26c6-4134-969d-762284e4c8fc

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionVolume/ProjectionCoefficients.lean:L11-L26
-- (upload_full_project.md Phase 4): solution for node OAI.Paper092.twice_sum_negative_eq_sum_abs. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_ProjectionVolume
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexGeometry
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexProjection
import Definitions.Def_OAI_Geometry_ProjectionVolume_ProductProjection

-- ---- from OAI.Geometry.ProjectionVolume.ProjectionCoefficients ----
namespace OAI

universe uι

open scoped BigOperators

namespace Paper092

theorem twice_sum_negative_eq_sum_abs {ι : Type uι} [Fintype ι] (v : ι → ℝ)
    (hv : ∑ i, v i = 0) :
    2 * (∑ i : {i // v i < 0}, -v i.val) = ∑ i, |v i| := by
  classical
  have hpoint (i : ι) : 2 * (if v i < 0 then -v i else 0) = |v i| - v i := by
    by_cases hi : v i < 0
    · simp [hi, abs_of_neg hi]
      ring
    · simp [hi, abs_of_nonneg (le_of_not_gt hi)]
  have hsum := congrArg (fun f : ι → ℝ => ∑ i, f i) (funext hpoint)
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib, hv, sub_zero] at hsum
  convert hsum using 1
  congr 1
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (Finset.univ.filter (fun i => v i < 0)) (by simp)
    (fun i => -v i)).symm

end Paper092

end OAI

-- ---- platform node ----
open OAI OAI.Paper092
universe uι
open scoped BigOperators

theorem solution {ι : Type uι} [Fintype ι] (v : ι → ℝ)
    (hv : ∑ i, v i = 0) :
    2 * (∑ i : {i // v i < 0}, -v i.val) = ∑ i, |v i| := by
  first
    | exact OAI.Paper092.twice_sum_negative_eq_sum_abs v hv
    | exact OAI.Paper092.twice_sum_negative_eq_sum_abs
    | (apply OAI.Paper092.twice_sum_negative_eq_sum_abs <;> assumption)
    | (intros; apply OAI.Paper092.twice_sum_negative_eq_sum_abs <;> assumption)
