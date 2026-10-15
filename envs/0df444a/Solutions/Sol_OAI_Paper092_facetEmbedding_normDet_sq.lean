-- Prove2me | solution 1 for OAI.Paper092.facetEmbedding_normDet_sq
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T21:36:44.175172+00:00
-- url     : https://prove2.me/submissions/fe74e57b-9157-4cd3-a906-60773c487817

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionVolume/FacetAreas.lean:L44-L60
-- (upload_full_project.md Phase 4): solution for node OAI.Paper092.facetEmbedding_normDet_sq. The node keeps its source
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

-- ---- from OAI.Geometry.ProjectionVolume.FacetAreas ----
namespace OAI

noncomputable section

open Set MeasureTheory
open scoped BigOperators RealInnerProductSpace ENNReal

namespace Paper092

theorem facetEmbedding_apply_same (n : ℕ) (i : Fin (n + 1)) (c : ℝ) (x : Euclidean n) :
    facetEmbedding n i c x i = c * ∑ j, x j := by
  simp [facetEmbedding]

theorem facetEmbedding_apply_succAbove (n : ℕ) (i : Fin (n + 1)) (c : ℝ)
    (x : Euclidean n) (j : Fin n) :
    facetEmbedding n i c x (i.succAbove j) = x j := by
  simp [facetEmbedding]

theorem facetEmbedding_inner (n : ℕ) (i : Fin (n + 1)) (c : ℝ) (x y : Euclidean n) :
    ⟪facetEmbedding n i c x, facetEmbedding n i c y⟫ =
      ⟪x, y⟫ + c ^ 2 * (∑ j, x j) * (∑ j, y j) := by
  rw [PiLp.inner_apply, Fin.sum_univ_succAbove _ i]
  simp only [facetEmbedding_apply_same, facetEmbedding_apply_succAbove, Real.inner_apply,
    PiLp.inner_apply]
  ring

theorem facetEmbedding_normDet_sq (n : ℕ) (i : Fin (n + 1)) (c : ℝ) :
    (facetEmbedding n i c).normDet ^ 2 = 1 + (n : ℝ) * c ^ 2 := by
  have hsq := (facetEmbedding n i c).normDet_sq_eq_det_gram (EuclideanSpace.basisFun (Fin n) ℝ)
  simp only [RCLike.ofReal_real_eq_id, id_eq] at hsq
  have hgram : Matrix.gram ℝ
      (fun j => facetEmbedding n i c (EuclideanSpace.basisFun (Fin n) ℝ j)) =
      1 + Matrix.replicateCol (Fin 1) (fun _ : Fin n => c) *
        Matrix.replicateRow (Fin 1) (fun _ : Fin n => c) := by
    ext j k
    simp only [Matrix.gram_apply, facetEmbedding_inner,
      (EuclideanSpace.basisFun (Fin n) ℝ).inner_eq_ite]
    simp [EuclideanSpace.basisFun_apply, PiLp.single_apply, Matrix.one_apply,
      Matrix.mul_apply, pow_two]
  rw [hgram] at hsq
  have hd := Matrix.det_one_add_replicateCol_mul_replicateRow (ι := Fin 1)
    (fun _ : Fin n => c) (fun _ : Fin n => c)
  simpa [dotProduct, pow_two, mul_assoc] using hsq.trans hd

end Paper092

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper092
open Set MeasureTheory
open scoped BigOperators RealInnerProductSpace ENNReal

theorem solution (n : ℕ) (i : Fin (n + 1)) (c : ℝ) :
    (facetEmbedding n i c).normDet ^ 2 = 1 + (n : ℝ) * c ^ 2 := by
  first
    | exact OAI.Paper092.facetEmbedding_normDet_sq n i c
    | exact OAI.Paper092.facetEmbedding_normDet_sq
    | (apply OAI.Paper092.facetEmbedding_normDet_sq <;> assumption)
    | (intros; apply OAI.Paper092.facetEmbedding_normDet_sq <;> assumption)
