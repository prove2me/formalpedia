-- Prove2me | solution 1 for OAI.Paper092.splitEuclideanProduct_preimage_vadd
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T21:41:35.558737+00:00
-- url     : https://prove2.me/submissions/3b764871-85ef-4281-a495-a2de907b2b5c

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionVolume/ProductFacetAreas.lean:L122-L141
-- (upload_full_project.md Phase 4): solution for node OAI.Paper092.splitEuclideanProduct_preimage_vadd. The node keeps its source
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
import Definitions.Def_OAI_Geometry_ProjectionVolume_ProductVolumeGeneral
import Definitions.Def_OAI_Geometry_ProjectionVolume_ProductFacetAreas

-- ---- from OAI.Geometry.ProjectionVolume.ProductFacetAreas ----
namespace OAI

noncomputable section

open Set MeasureTheory
open scoped BigOperators RealInnerProductSpace ENNReal Pointwise

namespace Paper092

theorem splitEuclideanProduct_preimage_vadd {r s : ℕ}
    (a : Euclidean r) (b : Euclidean s) (A : Set (Euclidean r)) (B : Set (Euclidean s)) :
    splitEuclideanProduct r s ⁻¹' ((a +ᵥ A) ×ˢ (b +ᵥ B)) =
      (splitEuclideanProduct r s).symm (a, b) +ᵥ
        (splitEuclideanProduct r s ⁻¹' (A ×ˢ B)) := by
  ext x
  constructor
  · rintro ⟨⟨a', ha, hea⟩, ⟨b', hb, heb⟩⟩
    refine ⟨(splitEuclideanProduct r s).symm (a', b'), ?_, ?_⟩
    · simpa only [Set.mem_preimage, ContinuousLinearEquiv.apply_symm_apply,
        Set.mem_prod] using And.intro ha hb
    · apply (splitEuclideanProduct r s).injective
      simp only [vadd_eq_add, map_add, ContinuousLinearEquiv.apply_symm_apply]
      exact Prod.ext hea heb
  · rintro ⟨y, hy, rfl⟩
    change (splitEuclideanProduct r s ((splitEuclideanProduct r s).symm (a, b) + y)).1 ∈
        a +ᵥ A ∧
      (splitEuclideanProduct r s ((splitEuclideanProduct r s).symm (a, b) + y)).2 ∈ b +ᵥ B
    simp only [map_add, ContinuousLinearEquiv.apply_symm_apply, Prod.fst_add, Prod.snd_add]
    exact ⟨⟨_, hy.1, rfl⟩, ⟨_, hy.2, rfl⟩⟩

end Paper092

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper092
open Set MeasureTheory
open scoped BigOperators RealInnerProductSpace ENNReal Pointwise

theorem solution {r s : ℕ}
    (a : Euclidean r) (b : Euclidean s) (A : Set (Euclidean r)) (B : Set (Euclidean s)) :
    splitEuclideanProduct r s ⁻¹' ((a +ᵥ A) ×ˢ (b +ᵥ B)) =
      (splitEuclideanProduct r s).symm (a, b) +ᵥ
        (splitEuclideanProduct r s ⁻¹' (A ×ˢ B)) := by
  first
    | exact OAI.Paper092.splitEuclideanProduct_preimage_vadd a b A B
    | exact OAI.Paper092.splitEuclideanProduct_preimage_vadd
    | (apply OAI.Paper092.splitEuclideanProduct_preimage_vadd <;> assumption)
    | (intros; apply OAI.Paper092.splitEuclideanProduct_preimage_vadd <;> assumption)
