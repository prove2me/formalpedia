-- Prove2me | solution 1 for OAI.Paper092.productFacet_brightness
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T21:50:47.360992+00:00
-- url     : https://prove2.me/submissions/2fced1b7-a95e-45fe-a843-332554ff6541

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionVolume/ProductBrightness.lean:L15-L63
-- (upload_full_project.md Phase 4): solution for node OAI.Paper092.productFacet_brightness. The node keeps its source
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
import Definitions.Def_OAI_Geometry_ProjectionVolume_ProjectionJacobian
import Theorems.Thm_OAI_Paper092_brightness_of_subset_affine_hyperplane
import Theorems.Thm_OAI_Paper092_facetEmbedding_normDet_sq
import Theorems.Thm_OAI_Paper092_facetEmbedding_zero_image
import Theorems.Thm_OAI_Paper092_simplexProduct_diagonal_facet_area_left
import Theorems.Thm_OAI_Paper092_simplexProduct_diagonal_facet_area_right
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

-- ---- from OAI.Geometry.ProjectionVolume.SimplexNormals ----
namespace OAI

noncomputable section

open Set MeasureTheory
open scoped RealInnerProductSpace

namespace Paper092

theorem diagonalVector_inner {d : ℕ} (u : Euclidean d) :
    ⟪diagonalVector d, u⟫ = ∑ i, u i := by
  simp [diagonalVector, EuclideanSpace.inner_eq_star_dotProduct, dotProduct]

theorem diagonalVector_norm (d : ℕ) : ‖diagonalVector d‖ = Real.sqrt d := by
  rw [← Real.sqrt_sq (norm_nonneg _), ← real_inner_self_eq_norm_sq, diagonalVector_inner]
  simp [diagonalVector]

theorem diagonalUnitNormal_norm (d : ℕ) (hd : 0 < d) : ‖diagonalUnitNormal d‖ = 1 := by
  rw [diagonalUnitNormal, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (Real.sqrt_nonneg _), diagonalVector_norm]
  exact inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast hd)))

theorem diagonalUnitNormal_inner {d : ℕ} (x : Euclidean d) :
    ⟪diagonalUnitNormal d, x⟫ = (∑ i, x i) / Real.sqrt d := by
  rw [diagonalUnitNormal, real_inner_smul_left, diagonalVector_inner]
  ring

theorem inner_diagonalUnitNormal {d : ℕ} (u : Euclidean d) :
    ⟪u, diagonalUnitNormal d⟫ = (∑ i, u i) / Real.sqrt d := by
  rw [real_inner_comm, diagonalUnitNormal_inner]

theorem coordinate_normal_norm {d : ℕ} (i : Fin d) :
    ‖EuclideanSpace.single i (1 : ℝ)‖ = 1 := by simp

theorem simplexFacet_coordinate_plane {d : ℕ} (i : Fin d) (x : Euclidean d)
    (hx : x ∈ simplexFacet d (some i)) :
    ⟪EuclideanSpace.single i (1 : ℝ), x⟫ = 0 := by
  simpa [EuclideanSpace.inner_single_left, simplexCoordinates] using hx.2

theorem simplexFacet_diagonal_plane {d : ℕ} (x : Euclidean d)
    (hx : x ∈ simplexFacet d none) :
    ⟪diagonalUnitNormal d, x⟫ = (Real.sqrt d)⁻¹ := by
  have hsum : ∑ i, x i = 1 := by
    have h := hx.2
    change 1 - ∑ i, x i = 0 at h
    linarith
  rw [diagonalUnitNormal_inner, hsum, one_div]

end Paper092

end

end OAI

-- ---- from OAI.Geometry.ProjectionVolume.ProductNormals ----
namespace OAI

noncomputable section

open Set
open scoped RealInnerProductSpace

namespace Paper092

theorem inner_splitBlocks (x y : Euclidean 20) :
    ⟪x, y⟫ = ⟪firstBlock x, firstBlock y⟫ + ⟪secondBlock x, secondBlock y⟫ := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  exact Fin.sum_univ_add (fun i : Fin (10 + 10) => y i * star (x i))

theorem firstBlock_liftFirst (x : Euclidean 10) : firstBlock (liftFirst x) = x := by
  change (splitBlocks (splitBlocks.symm (x, 0))).1 = x
  simp

theorem secondBlock_liftFirst (x : Euclidean 10) : secondBlock (liftFirst x) = 0 := by
  change (splitBlocks (splitBlocks.symm (x, 0))).2 = 0
  simp

theorem firstBlock_liftSecond (x : Euclidean 10) : firstBlock (liftSecond x) = 0 := by
  change (splitBlocks (splitBlocks.symm (0, x))).1 = 0
  simp

theorem secondBlock_liftSecond (x : Euclidean 10) : secondBlock (liftSecond x) = x := by
  change (splitBlocks (splitBlocks.symm (0, x))).2 = x
  simp

theorem inner_liftFirst (x : Euclidean 20) (y : Euclidean 10) :
    ⟪x, liftFirst y⟫ = ⟪firstBlock x, y⟫ := by
  rw [inner_splitBlocks, firstBlock_liftFirst, secondBlock_liftFirst, inner_zero_right, add_zero]

theorem inner_liftSecond (x : Euclidean 20) (y : Euclidean 10) :
    ⟪x, liftSecond y⟫ = ⟪secondBlock x, y⟫ := by
  rw [inner_splitBlocks, firstBlock_liftSecond, secondBlock_liftSecond, inner_zero_right, zero_add]

theorem liftFirst_norm (x : Euclidean 10) : ‖liftFirst x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← real_inner_self_eq_norm_sq, inner_liftFirst, firstBlock_liftFirst,
    real_inner_self_eq_norm_sq]

theorem liftSecond_norm (x : Euclidean 10) : ‖liftSecond x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← real_inner_self_eq_norm_sq, inner_liftSecond, secondBlock_liftSecond,
    real_inner_self_eq_norm_sq]

theorem productFacet_left_coordinate_plane (i : Fin 10) (x : Euclidean 20)
    (hx : x ∈ productFacet (.inl (some i))) :
    ⟪liftFirst (EuclideanSpace.single i (1 : ℝ)), x⟫ = 0 := by
  rw [real_inner_comm, inner_liftFirst, real_inner_comm]
  exact simplexFacet_coordinate_plane i (firstBlock x) ⟨hx.1.1, hx.2⟩

theorem productFacet_right_coordinate_plane (i : Fin 10) (x : Euclidean 20)
    (hx : x ∈ productFacet (.inr (some i))) :
    ⟪liftSecond (EuclideanSpace.single i (1 : ℝ)), x⟫ = 0 := by
  rw [real_inner_comm, inner_liftSecond, real_inner_comm]
  exact simplexFacet_coordinate_plane i (secondBlock x) ⟨hx.1.2, hx.2⟩

theorem productFacet_left_diagonal_plane (x : Euclidean 20)
    (hx : x ∈ productFacet (.inl none)) :
    ⟪liftFirst (diagonalUnitNormal 10), x⟫ = (Real.sqrt 10)⁻¹ := by
  rw [real_inner_comm, inner_liftFirst, real_inner_comm]
  exact simplexFacet_diagonal_plane (firstBlock x) ⟨hx.1.1, hx.2⟩

theorem productFacet_right_diagonal_plane (x : Euclidean 20)
    (hx : x ∈ productFacet (.inr none)) :
    ⟪liftSecond (diagonalUnitNormal 10), x⟫ = (Real.sqrt 10)⁻¹ := by
  rw [real_inner_comm, inner_liftSecond, real_inner_comm]
  exact simplexFacet_diagonal_plane (secondBlock x) ⟨hx.1.2, hx.2⟩

end Paper092

end

end OAI

-- ---- from OAI.Geometry.ProjectionVolume.FacetAreas ----
namespace OAI

noncomputable section

open Set MeasureTheory
open scoped BigOperators RealInnerProductSpace ENNReal

namespace Paper092

theorem facetEmbedding_normDet_zero (n : ℕ) (i : Fin (n + 1)) :
    (facetEmbedding n i 0).normDet = 1 := by
  have h := facetEmbedding_normDet_sq n i 0
  have hp := (facetEmbedding n i 0).normDet_nonneg
  nlinarith

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

theorem simplexProduct_coordinate_facet_area_left (r s : ℕ) (i : Fin (r + 1)) :
    μHE[r + s] (splitEuclideanProduct (r + 1) s ⁻¹'
      (simplexFacet (r + 1) (some i) ×ˢ standardSimplex s)) =
      ENNReal.ofReal ((1 / (Nat.factorial r : ℝ)) * (1 / (Nat.factorial s : ℝ))) := by
  have h := euclideanProductMap_image_area (facetEmbedding r i 0)
    (LinearMap.id : Euclidean s →ₗ[ℝ] Euclidean s)
    (standardSimplex r) (standardSimplex s)
    (standardSimplex_isCompact r).measurableSet (standardSimplex_isCompact s).measurableSet
  simpa only [facetEmbedding_zero_image, LinearMap.id_coe, Set.image_id,
    facetEmbedding_normDet_zero, LinearMap.normDet_id, one_mul, ENNReal.ofReal_one,
    standardSimplex_volume, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / (Nat.factorial r : ℝ))]
    using h

theorem simplexProduct_coordinate_facet_area_right (r s : ℕ) (i : Fin (s + 1)) :
    μHE[r + s] (splitEuclideanProduct r (s + 1) ⁻¹'
      (standardSimplex r ×ˢ simplexFacet (s + 1) (some i))) =
      ENNReal.ofReal ((1 / (Nat.factorial r : ℝ)) * (1 / (Nat.factorial s : ℝ))) := by
  have h := euclideanProductMap_image_area
    (LinearMap.id : Euclidean r →ₗ[ℝ] Euclidean r) (facetEmbedding s i 0)
    (standardSimplex r) (standardSimplex s)
    (standardSimplex_isCompact r).measurableSet (standardSimplex_isCompact s).measurableSet
  simpa only [facetEmbedding_zero_image, LinearMap.id_coe, Set.image_id,
    facetEmbedding_normDet_zero, LinearMap.normDet_id, one_mul, ENNReal.ofReal_one,
    standardSimplex_volume, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / (Nat.factorial r : ℝ))]
    using h

end Paper092

end

end OAI

-- ---- from OAI.Geometry.ProjectionVolume.ProductFacetGeometry ----
namespace OAI

open Set

namespace Paper092

theorem productFacet_inl_eq_preimage (a : Option (Fin 10)) :
    productFacet (.inl a) = splitBlocks ⁻¹' (simplexFacet 10 a ×ˢ standardSimplex 10) := by
  ext x
  change ((firstBlock x ∈ standardSimplex 10 ∧ secondBlock x ∈ standardSimplex 10) ∧
    simplexCoordinates (firstBlock x) a = 0) ↔
      ((firstBlock x ∈ standardSimplex 10 ∧ simplexCoordinates (firstBlock x) a = 0) ∧
        secondBlock x ∈ standardSimplex 10)
  exact ⟨fun ⟨⟨hx, hy⟩, ha⟩ => ⟨⟨hx, ha⟩, hy⟩,
    fun ⟨⟨hx, ha⟩, hy⟩ => ⟨⟨hx, hy⟩, ha⟩⟩

theorem productFacet_inr_eq_preimage (a : Option (Fin 10)) :
    productFacet (.inr a) = splitBlocks ⁻¹' (standardSimplex 10 ×ˢ simplexFacet 10 a) := by
  ext x
  change ((firstBlock x ∈ standardSimplex 10 ∧ secondBlock x ∈ standardSimplex 10) ∧
    simplexCoordinates (secondBlock x) a = 0) ↔
      (firstBlock x ∈ standardSimplex 10 ∧
        (secondBlock x ∈ standardSimplex 10 ∧ simplexCoordinates (secondBlock x) a = 0))
  exact and_assoc

end Paper092

end OAI

-- ---- from OAI.Geometry.ProjectionVolume.ProductFacetAreaValues ----
namespace OAI

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace Paper092

theorem splitEuclideanProduct_ten_ten : splitEuclideanProduct 10 10 = splitBlocks := rfl

theorem productFacet_inl_some_area (i : Fin 10) :
    μHE[19] (productFacet (.inl (some i))) =
      ENNReal.ofReal (1 / ((Nat.factorial 9 : ℝ) * (Nat.factorial 10 : ℝ))) := by
  rw [productFacet_inl_eq_preimage, ← splitEuclideanProduct_ten_ten]
  rw [simplexProduct_coordinate_facet_area_left 9 10 i]
  congr 1
  simp only [one_div, mul_inv_rev]
  ring

theorem productFacet_inr_some_area (i : Fin 10) :
    μHE[19] (productFacet (.inr (some i))) =
      ENNReal.ofReal (1 / ((Nat.factorial 9 : ℝ) * (Nat.factorial 10 : ℝ))) := by
  rw [productFacet_inr_eq_preimage, ← splitEuclideanProduct_ten_ten]
  rw [simplexProduct_coordinate_facet_area_right 10 9 i]
  congr 1
  simp only [one_div, mul_inv_rev]

theorem productFacet_inl_none_area :
    μHE[19] (productFacet (.inl none)) =
      ENNReal.ofReal (Real.sqrt 10 / ((Nat.factorial 9 : ℝ) * (Nat.factorial 10 : ℝ))) := by
  rw [productFacet_inl_eq_preimage, ← splitEuclideanProduct_ten_ten]
  rw [simplexProduct_diagonal_facet_area_left 9 10]
  congr 1
  norm_num only [Nat.cast_ofNat]
  simp only [div_eq_mul_inv]
  ring

theorem productFacet_inr_none_area :
    μHE[19] (productFacet (.inr none)) =
      ENNReal.ofReal (Real.sqrt 10 / ((Nat.factorial 9 : ℝ) * (Nat.factorial 10 : ℝ))) := by
  rw [productFacet_inr_eq_preimage, ← splitEuclideanProduct_ten_ten]
  rw [simplexProduct_diagonal_facet_area_right 10 9]
  congr 1
  norm_num only [Nat.cast_ofNat]
  simp only [div_eq_mul_inv]
  ring

end Paper092

end

end OAI

-- ---- from OAI.Geometry.ProjectionVolume.ProductBrightness ----
namespace OAI

noncomputable section

open Set MeasureTheory
open scoped RealInnerProductSpace

namespace Paper092

theorem productFacet_brightness (a : ProductFacetIndex) (u : Euclidean 20) :
    brightness (productFacet a) u =
      |productVelocity u a| / ((Nat.factorial 9 : ℝ) * (Nat.factorial 10 : ℝ)) := by
  have hsqrt : 0 < Real.sqrt (10 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  cases a with
  | inl a =>
    cases a with
    | none =>
      have hn : ‖liftFirst (diagonalUnitNormal 10)‖ = 1 := by
        rw [liftFirst_norm]
        exact diagonalUnitNormal_norm 10 (by norm_num)
      rw [brightness_of_subset_affine_hyperplane u (liftFirst (diagonalUnitNormal 10))
        hn (Real.sqrt 10)⁻¹ _ productFacet_left_diagonal_plane]
      rw [show 20 - 1 = 19 by rfl, productFacet_inl_none_area,
        ENNReal.toReal_ofReal (by positivity), inner_liftFirst, inner_diagonalUnitNormal]
      simp only [productVelocity, simplexVelocity, abs_neg, abs_div, Nat.cast_ofNat,
        abs_of_pos hsqrt]
      field_simp
    | some i =>
      have hn : ‖liftFirst (EuclideanSpace.single i (1 : ℝ))‖ = 1 := by
        rw [liftFirst_norm, coordinate_normal_norm]
      rw [brightness_of_subset_affine_hyperplane u (liftFirst (EuclideanSpace.single i 1))
        hn 0 _ (productFacet_left_coordinate_plane i)]
      rw [show 20 - 1 = 19 by rfl, productFacet_inl_some_area,
        ENNReal.toReal_ofReal (by positivity)]
      simp [inner_liftFirst, EuclideanSpace.inner_single_right, productVelocity,
        simplexVelocity, div_eq_mul_inv]
  | inr a =>
    cases a with
    | none =>
      have hn : ‖liftSecond (diagonalUnitNormal 10)‖ = 1 := by
        rw [liftSecond_norm]
        exact diagonalUnitNormal_norm 10 (by norm_num)
      rw [brightness_of_subset_affine_hyperplane u (liftSecond (diagonalUnitNormal 10))
        hn (Real.sqrt 10)⁻¹ _ productFacet_right_diagonal_plane]
      rw [show 20 - 1 = 19 by rfl, productFacet_inr_none_area,
        ENNReal.toReal_ofReal (by positivity), inner_liftSecond, inner_diagonalUnitNormal]
      simp only [productVelocity, simplexVelocity, abs_neg, abs_div, Nat.cast_ofNat,
        abs_of_pos hsqrt]
      field_simp
    | some i =>
      have hn : ‖liftSecond (EuclideanSpace.single i (1 : ℝ))‖ = 1 := by
        rw [liftSecond_norm, coordinate_normal_norm]
      rw [brightness_of_subset_affine_hyperplane u (liftSecond (EuclideanSpace.single i 1))
        hn 0 _ (productFacet_right_coordinate_plane i)]
      rw [show 20 - 1 = 19 by rfl, productFacet_inr_some_area,
        ENNReal.toReal_ofReal (by positivity)]
      simp [inner_liftSecond, EuclideanSpace.inner_single_right, productVelocity,
        simplexVelocity, div_eq_mul_inv]

end Paper092

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper092
open Set MeasureTheory
open scoped RealInnerProductSpace

theorem solution (a : ProductFacetIndex) (u : Euclidean 20) :
    brightness (productFacet a) u =
      |productVelocity u a| / ((Nat.factorial 9 : ℝ) * (Nat.factorial 10 : ℝ)) := by
  first
    | exact OAI.Paper092.productFacet_brightness a u
    | exact OAI.Paper092.productFacet_brightness
    | (apply OAI.Paper092.productFacet_brightness <;> assumption)
    | (intros; apply OAI.Paper092.productFacet_brightness <;> assumption)
