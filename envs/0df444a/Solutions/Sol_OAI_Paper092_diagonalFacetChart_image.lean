-- Prove2me | solution 1 for OAI.Paper092.diagonalFacetChart_image
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T21:40:03.187138+00:00
-- url     : https://prove2.me/submissions/ea9470fd-5d79-4427-a4fa-428b141a66dc

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionVolume/FacetAreas.lean:L113-L139
-- (upload_full_project.md Phase 4): solution for node OAI.Paper092.diagonalFacetChart_image. The node keeps its source
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
import Definitions.Def_OAI_Geometry_ProjectionVolume_FacetAreas
import Theorems.Thm_OAI_Paper092_mem_standardSimplex_iff

-- ---- from OAI.Geometry.ProjectionVolume.FacetAreas ----
namespace OAI

noncomputable section

open Set MeasureTheory
open scoped BigOperators RealInnerProductSpace ENNReal

namespace Paper092

theorem diagonalFacetChart_image (n : ℕ) (i : Fin (n + 1)) :
    diagonalFacetChart n i '' standardSimplex n = simplexFacet (n + 1) none := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_standardSimplex_iff] at hx
    change diagonalFacetChart n i x ∈ standardSimplex (n + 1) ∧
      1 - ∑ j, diagonalFacetChart n i x j = 0
    rw [mem_standardSimplex_iff]
    simp [diagonalFacetChart, Fin.forall_iff_succAbove i]
    exact ⟨hx.2, hx.1⟩
  · rintro ⟨hy, hi⟩
    change 1 - ∑ j, y j = 0 at hi
    have htotal : ∑ j, y j = 1 := by linarith
    rw [mem_standardSimplex_iff] at hy
    have hsum := Fin.add_sum_removeNth i (fun j => y j)
    refine ⟨WithLp.toLp 2 (i.removeNth y), ?_, ?_⟩
    · rw [mem_standardSimplex_iff]
      refine ⟨fun j => hy.1 (i.succAbove j), ?_⟩
      change ∑ j, i.removeNth (fun k => y k) j ≤ 1
      linarith [hy.1 i]
    · ext j
      induction j using i.succAboveCases
      · simp only [diagonalFacetChart, PiLp.toLp_apply, Fin.insertNth_apply_same]
        change 1 - ∑ j, i.removeNth (fun k => y k) j = y i
        linarith
      · simp [diagonalFacetChart]

end Paper092

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper092
open Set MeasureTheory
open scoped BigOperators RealInnerProductSpace ENNReal

theorem solution (n : ℕ) (i : Fin (n + 1)) :
    diagonalFacetChart n i '' standardSimplex n = simplexFacet (n + 1) none := by
  first
    | exact OAI.Paper092.diagonalFacetChart_image n i
    | exact OAI.Paper092.diagonalFacetChart_image
    | (apply OAI.Paper092.diagonalFacetChart_image <;> assumption)
    | (intros; apply OAI.Paper092.diagonalFacetChart_image <;> assumption)
