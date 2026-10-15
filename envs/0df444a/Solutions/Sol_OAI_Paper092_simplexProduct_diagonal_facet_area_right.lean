-- Prove2me | solution 1 for OAI.Paper092.simplexProduct_diagonal_facet_area_right
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T21:44:57.962486+00:00
-- url     : https://prove2.me/submissions/0ad45ebd-6845-4ce3-ace8-58ed666db830

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionVolume/ProductFacetAreas.lean:L199-L215
-- (upload_full_project.md Phase 4): solution for node OAI.Paper092.simplexProduct_diagonal_facet_area_right. The node keeps its source
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
import Theorems.Thm_OAI_Paper092_diagonalFacetChart_image
import Theorems.Thm_OAI_Paper092_facetEmbedding_normDet_sq
import Theorems.Thm_OAI_Paper092_splitEuclideanProduct_preimage_vadd
import Theorems.Thm_OAI_Paper092_standardSimplex_volume

-- ---- from OAI.Geometry.ProjectionVolume.SimplexGeometry ----
namespace OAI

noncomputable section

open Set MeasureTheory

namespace Paper092

theorem standardSimplex_isCompact (n : ℕ) : IsCompact (standardSimplex n) :=
  ((Set.finite_range _).insert 0).isCompact_convexHull ℝ

end Paper092

end

end OAI

-- ---- from OAI.Geometry.ProjectionVolume.FacetAreas ----
namespace OAI

noncomputable section

open Set MeasureTheory
open scoped BigOperators RealInnerProductSpace ENNReal

namespace Paper092

theorem facetEmbedding_normDet_neg_one (n : ℕ) (i : Fin (n + 1)) :
    (facetEmbedding n i (-1)).normDet = Real.sqrt (n + 1) := by
  have h := facetEmbedding_normDet_sq n i (-1)
  have hp := (facetEmbedding n i (-1)).normDet_nonneg
  have hs := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n + 1)
  have hsp := Real.sqrt_nonneg ((n : ℝ) + 1)
  nlinarith

theorem diagonalFacetChart_eq (n : ℕ) (i : Fin (n + 1)) (x : Euclidean n) :
    diagonalFacetChart n i x = facetEmbedding n i (-1) x + EuclideanSpace.single i 1 := by
  ext j
  induction j using i.succAboveCases <;>
    simp [diagonalFacetChart, facetEmbedding, sub_eq_add_neg, add_comm]

end Paper092

end

end OAI

-- ---- from OAI.Geometry.ProjectionVolume.ProductVolumeGeneral ----
namespace OAI

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace Paper092

theorem splitEuclideanProduct_measurePreserving (r s : ℕ) :
    MeasurePreserving (splitEuclideanProduct r s) volume volume := by
  have h₁ := PiLp.volume_preserving_ofLp (Fin (r + s))
  have h₂ := (volume_measurePreserving_piCongrLeft (fun _ : Fin (r + s) => ℝ)
    (finSumFinEquiv : Fin r ⊕ Fin s ≃ Fin (r + s))).symm
  have h₃ := volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin r ⊕ Fin s => ℝ)
  have h₄ := (PiLp.volume_preserving_toLp (Fin r)).prod
    (PiLp.volume_preserving_toLp (Fin s))
  convert h₄.comp (h₃.comp (h₂.comp h₁)) using 1
  all_goals rfl

theorem splitEuclideanProduct_volume (r s : ℕ) (A : Set (Euclidean r))
    (B : Set (Euclidean s)) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    volume (splitEuclideanProduct r s ⁻¹' (A ×ˢ B)) = volume A * volume B := by
  rw [(splitEuclideanProduct_measurePreserving r s).measure_preimage
    (hA.prod hB).nullMeasurableSet]
  exact Measure.prod_prod _ _

end Paper092

end

end OAI

-- ---- from OAI.Geometry.ProjectionVolume.ProductFacetAreas ----
namespace OAI

noncomputable section

open Set MeasureTheory
open scoped BigOperators RealInnerProductSpace ENNReal Pointwise

namespace Paper092

theorem splitEuclideanProductL2_apply (r s : ℕ) (x : Euclidean (r + s)) :
    splitEuclideanProductL2 r s x = WithLp.toLp 2 (splitEuclideanProduct r s x) := rfl

theorem euclideanProductMap_apply {r s t u : ℕ} (f : Euclidean r →ₗ[ℝ] Euclidean t)
    (g : Euclidean s →ₗ[ℝ] Euclidean u) (x : Euclidean (r + s)) :
    euclideanProductMap f g x = (splitEuclideanProduct t u).symm
      (f (splitEuclideanProduct r s x).1, g (splitEuclideanProduct r s x).2) := rfl

theorem splitEuclideanProduct_inner (r s : ℕ) (x y : Euclidean (r + s)) :
    ⟪x, y⟫ = ⟪(splitEuclideanProduct r s x).1, (splitEuclideanProduct r s y).1⟫ +
      ⟪(splitEuclideanProduct r s x).2, (splitEuclideanProduct r s y).2⟫ := by
  symm
  exact (splitEuclideanProductL2 r s).inner_map_map x y

theorem euclideanProductMap_inner {r s t u : ℕ} (f : Euclidean r →ₗ[ℝ] Euclidean t)
    (g : Euclidean s →ₗ[ℝ] Euclidean u) (x y : Euclidean (r + s)) :
    ⟪euclideanProductMap f g x, euclideanProductMap f g y⟫ =
      ⟪f (splitEuclideanProduct r s x).1, f (splitEuclideanProduct r s y).1⟫ +
      ⟪g (splitEuclideanProduct r s x).2, g (splitEuclideanProduct r s y).2⟫ := by
  rw [splitEuclideanProduct_inner t u]
  simp only [euclideanProductMap_apply, ContinuousLinearEquiv.apply_symm_apply]

theorem split_productOrthonormalBasis_inl (r s : ℕ) (i : Fin r) :
    splitEuclideanProduct r s (productOrthonormalBasis r s (.inl i)) =
      (EuclideanSpace.basisFun (Fin r) ℝ i, 0) := by
  have h := (splitEuclideanProductL2 r s).apply_symm_apply
    (((EuclideanSpace.basisFun (Fin r) ℝ).prod (EuclideanSpace.basisFun (Fin s) ℝ)) (.inl i))
  simpa only [productOrthonormalBasis, OrthonormalBasis.map_apply,
    OrthonormalBasis.prod_apply, Sum.elim_inl, Function.comp_apply,
    LinearMap.inl_apply, splitEuclideanProductL2_apply] using congrArg WithLp.ofLp h

theorem split_productOrthonormalBasis_inr (r s : ℕ) (i : Fin s) :
    splitEuclideanProduct r s (productOrthonormalBasis r s (.inr i)) =
      (0, EuclideanSpace.basisFun (Fin s) ℝ i) := by
  have h := (splitEuclideanProductL2 r s).apply_symm_apply
    (((EuclideanSpace.basisFun (Fin r) ℝ).prod (EuclideanSpace.basisFun (Fin s) ℝ)) (.inr i))
  simpa only [productOrthonormalBasis, OrthonormalBasis.map_apply,
    OrthonormalBasis.prod_apply, Sum.elim_inr, Function.comp_apply,
    LinearMap.inr_apply, splitEuclideanProductL2_apply] using congrArg WithLp.ofLp h

theorem euclideanProductMap_normDet {r s t u : ℕ} (f : Euclidean r →ₗ[ℝ] Euclidean t)
    (g : Euclidean s →ₗ[ℝ] Euclidean u) :
    (euclideanProductMap f g).normDet = f.normDet * g.normDet := by
  have hgram : Matrix.gram ℝ (fun i => euclideanProductMap f g (productOrthonormalBasis r s i)) =
      Matrix.fromBlocks
        (Matrix.gram ℝ (fun i => f (EuclideanSpace.basisFun (Fin r) ℝ i))) 0 0
        (Matrix.gram ℝ (fun i => g (EuclideanSpace.basisFun (Fin s) ℝ i))) := by
    ext i j
    cases i <;> cases j <;>
      simp [Matrix.gram_apply, euclideanProductMap_inner,
        split_productOrthonormalBasis_inl, split_productOrthonormalBasis_inr]
  have h := (euclideanProductMap f g).normDet_sq_eq_det_gram (productOrthonormalBasis r s)
  have hf := f.normDet_sq_eq_det_gram (EuclideanSpace.basisFun (Fin r) ℝ)
  have hg := g.normDet_sq_eq_det_gram (EuclideanSpace.basisFun (Fin s) ℝ)
  simp only [RCLike.ofReal_real_eq_id, id_eq] at h hf hg
  rw [hgram, Matrix.det_fromBlocks_zero₂₁, ← hf, ← hg] at h
  have hn := (euclideanProductMap f g).normDet_nonneg
  have hp := mul_nonneg f.normDet_nonneg g.normDet_nonneg
  nlinarith

theorem euclideanProductMap_image {r s t u : ℕ} (f : Euclidean r →ₗ[ℝ] Euclidean t)
    (g : Euclidean s →ₗ[ℝ] Euclidean u) (A : Set (Euclidean r)) (B : Set (Euclidean s)) :
    euclideanProductMap f g '' (splitEuclideanProduct r s ⁻¹' (A ×ˢ B)) =
      splitEuclideanProduct t u ⁻¹' ((f '' A) ×ˢ (g '' B)) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change (splitEuclideanProduct t u (euclideanProductMap f g x)).1 ∈ f '' A ∧
      (splitEuclideanProduct t u (euclideanProductMap f g x)).2 ∈ g '' B
    rw [euclideanProductMap_apply, ContinuousLinearEquiv.apply_symm_apply]
    exact ⟨⟨_, hx.1, rfl⟩, ⟨_, hx.2, rfl⟩⟩
  · rintro ⟨⟨a, ha, hea⟩, ⟨b, hb, heb⟩⟩
    refine ⟨(splitEuclideanProduct r s).symm (a, b), ?_, ?_⟩
    · simpa only [Set.mem_preimage, ContinuousLinearEquiv.apply_symm_apply,
        Set.mem_prod] using And.intro ha hb
    · apply (splitEuclideanProduct t u).injective
      simp only [euclideanProductMap_apply, ContinuousLinearEquiv.apply_symm_apply,
        hea, heb, Prod.mk.eta]

theorem euclideanProductMap_image_area {r s t u : ℕ}
    (f : Euclidean r →ₗ[ℝ] Euclidean t) (g : Euclidean s →ₗ[ℝ] Euclidean u)
    (A : Set (Euclidean r)) (B : Set (Euclidean s))
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    μHE[r + s] (splitEuclideanProduct t u ⁻¹' ((f '' A) ×ˢ (g '' B))) =
      ENNReal.ofReal (f.normDet * g.normDet) * (volume A * volume B) := by
  have h := (euclideanProductMap f g).euclideanHausdorffMeasure_image_eq_normDet_mul_volume
    (splitEuclideanProduct r s ⁻¹' (A ×ˢ B))
  simpa only [finrank_euclideanSpace_fin, euclideanProductMap_image,
    euclideanProductMap_normDet, splitEuclideanProduct_volume r s A B hA hB] using h

theorem simplexFacet_diagonal_eq_vadd (n : ℕ) (i : Fin (n + 1)) :
    simplexFacet (n + 1) none = EuclideanSpace.single i (1 : ℝ) +ᵥ
      (facetEmbedding n i (-1) '' standardSimplex n) := by
  rw [← diagonalFacetChart_image n i]
  change diagonalFacetChart n i '' standardSimplex n =
    (fun x => EuclideanSpace.single i (1 : ℝ) + x) ''
      (facetEmbedding n i (-1) '' standardSimplex n)
  rw [image_image]
  congr 1
  funext x
  exact (diagonalFacetChart_eq n i x).trans (add_comm _ _)

theorem simplexProduct_diagonal_facet_area_right (r s : ℕ) :
    μHE[r + s] (splitEuclideanProduct r (s + 1) ⁻¹'
      (standardSimplex r ×ˢ simplexFacet (s + 1) none)) =
      ENNReal.ofReal (Real.sqrt (s + 1) *
        ((1 / (Nat.factorial r : ℝ)) * (1 / (Nat.factorial s : ℝ)))) := by
  let i : Fin (s + 1) := Fin.last s
  rw [simplexFacet_diagonal_eq_vadd s i]
  rw [← zero_vadd (Euclidean r) (standardSimplex r)]
  rw [splitEuclideanProduct_preimage_vadd, measure_vadd]
  have h := euclideanProductMap_image_area
    (LinearMap.id : Euclidean r →ₗ[ℝ] Euclidean r) (facetEmbedding s i (-1))
    (standardSimplex r) (standardSimplex s)
    (standardSimplex_isCompact r).measurableSet (standardSimplex_isCompact s).measurableSet
  simpa only [LinearMap.id_coe, Set.image_id, facetEmbedding_normDet_neg_one,
    LinearMap.normDet_id, one_mul, standardSimplex_volume,
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / (Nat.factorial r : ℝ)),
    ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)] using h

end Paper092

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper092
open Set MeasureTheory
open scoped BigOperators RealInnerProductSpace ENNReal Pointwise

theorem solution (r s : ℕ) :
    μHE[r + s] (splitEuclideanProduct r (s + 1) ⁻¹'
      (standardSimplex r ×ˢ simplexFacet (s + 1) none)) =
      ENNReal.ofReal (Real.sqrt (s + 1) *
        ((1 / (Nat.factorial r : ℝ)) * (1 / (Nat.factorial s : ℝ)))) := by
  first
    | exact OAI.Paper092.simplexProduct_diagonal_facet_area_right r s
    | exact OAI.Paper092.simplexProduct_diagonal_facet_area_right
    | (apply OAI.Paper092.simplexProduct_diagonal_facet_area_right <;> assumption)
    | (intros; apply OAI.Paper092.simplexProduct_diagonal_facet_area_right <;> assumption)
