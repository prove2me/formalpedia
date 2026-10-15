-- Prove2me | solution 1 for OAI.Paper092.facetEmbedding_zero_image
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T21:37:53.565552+00:00
-- url     : https://prove2.me/submissions/96f20609-358a-4bf8-a84f-47799419277c

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionVolume/FacetAreas.lean:L76-L93
-- (upload_full_project.md Phase 4): solution for node OAI.Paper092.facetEmbedding_zero_image. The node keeps its source
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

theorem facetEmbedding_zero_image (n : ℕ) (i : Fin (n + 1)) :
    facetEmbedding n i 0 '' standardSimplex n = simplexFacet (n + 1) (some i) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change facetEmbedding n i 0 x ∈ standardSimplex (n + 1) ∧
      facetEmbedding n i 0 x i = 0
    rw [mem_standardSimplex_iff] at hx ⊢
    simp [facetEmbedding, Fin.forall_iff_succAbove i, hx]
  · rintro ⟨hy, hi⟩
    change y i = 0 at hi
    refine ⟨WithLp.toLp 2 (i.removeNth y), ?_, ?_⟩
    · rw [mem_standardSimplex_iff] at hy ⊢
      refine ⟨fun j => hy.1 (i.succAbove j), ?_⟩
      have hsum := Fin.add_sum_removeNth i (fun j => y j)
      simpa [hi, Fin.removeNth] using hsum.trans_le hy.2
    · ext j
      induction j using i.succAboveCases <;> simp [facetEmbedding, hi]

end Paper092

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper092
open Set MeasureTheory
open scoped BigOperators RealInnerProductSpace ENNReal

theorem solution (n : ℕ) (i : Fin (n + 1)) :
    facetEmbedding n i 0 '' standardSimplex n = simplexFacet (n + 1) (some i) := by
  first
    | exact OAI.Paper092.facetEmbedding_zero_image n i
    | exact OAI.Paper092.facetEmbedding_zero_image
    | (apply OAI.Paper092.facetEmbedding_zero_image <;> assumption)
    | (intros; apply OAI.Paper092.facetEmbedding_zero_image <;> assumption)
