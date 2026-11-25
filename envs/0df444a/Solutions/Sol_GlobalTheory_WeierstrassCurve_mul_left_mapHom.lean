-- Prove2me | solution 1 for GlobalTheory.WeierstrassCurve.mul_left_mapHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:16:13.135489+00:00
-- url     : https://prove2.me/submissions/e7d69161-5dfe-4100-81ee-7d4454add65c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IrrelevantLeMapLinearGradedMap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsLiftAddOfIsReducedEq
import Theorems.Thm_GlobalTheory_WeierstrassCurve_eq_classifyingHom
import Theorems.Thm_GlobalTheory_AddLaw_Proportional_symm
import Theorems.Thm_GlobalTheory_ProjPoint_hom_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
universe u
noncomputable section
open GlobalTheory
open GlobalTheory.WeierstrassCurve
open AddLaw
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable [W.IsElliptic]
variable {R' : Type u} [CommRing R'] {W' : WeierstrassCurve R'} [W'.IsElliptic] (f : R →+* R')
  (h : W.map f = W')
namespace GlobalTheory.WeierstrassCurve
theorem _root_.solution {T' : Over (Spec (.of R'))} {T : Over (Spec (.of R))}
    (t : T'.left ⟶ T.left) {x' y' : T' ⟶ schemeOver W'} {x y : T ⟶ schemeOver W}
    (hx : x'.left ≫ mapHom W f h = t ≫ x.left) (hy : y'.left ≫ mapHom W f h = t ≫ y.left) :
    (x' * y').left ≫ mapHom W f h = t ≫ (x * y).left := by
  have e : mapHom W f h ≫ mapHom universalCurve (classifyingHom W) (map_classifyingHom W) =
      mapHom universalCurve (classifyingHom W') (map_classifyingHom W') := by
    rw [mapHom_comp]
    congr 1
    exact eq_classifyingHom W' ((map_comp_eq (map_classifyingHom W) f).trans h)
  refine (isPullback_universalCurve W).hom_ext ?_ ?_
  · have e₁ := mul_left_mapHom_universal W (𝟙 T.left)
      (x := pullbackPointEquiv (isPullback_universalCurve W) T x)
      (y := pullbackPointEquiv (isPullback_universalCurve W) T y) (x' := x) (y' := y)
      (Category.id_comp _).symm (Category.id_comp _).symm
    have e₂ := mul_left_mapHom_universal W' t
      (x := pullbackPointEquiv (isPullback_universalCurve W) T x)
      (y := pullbackPointEquiv (isPullback_universalCurve W) T y) (x' := x') (y' := y')
      (by rw [← e, reassoc_of% hx]; rfl) (by rw [← e, reassoc_of% hy]; rfl)
    refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) e).trans (e₂.trans ?_))
    exact ((Category.assoc _ _ _).trans (congrArg (t ≫ ·) (e₁.trans (Category.id_comp _)))).symm
  · have w : ∀ z : T' ⟶ schemeOver W', (z.left ≫ mapHom W f h) ≫ (schemeOver W).hom =
        T'.hom ≫ Spec.map (CommRingCat.ofHom f) := fun z =>
      (Category.assoc _ _ _).trans ((congrArg (z.left ≫ ·) (mapHom_toSpec W f h)).trans
        (Over.w_assoc z _))
    rw [w, ← w x', hx, Category.assoc, Category.assoc, Over.w, Over.w]
end GlobalTheory.WeierstrassCurve
