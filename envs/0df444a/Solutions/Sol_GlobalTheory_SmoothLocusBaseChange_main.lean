-- Prove2me | solution 1 for GlobalTheory.SmoothLocusBaseChange.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:53:50.412634+00:00
-- url     : https://prove2.me/submissions/9195c79a-7201-4e44-844b-ffc6772cb673

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_LiftMulHomPullbackFst
import Theorems.Thm_GlobalTheory_SmoothLocusBaseChange_lift_mul_hom_pullback_fst
import Theorems.Thm_GlobalTheory_ProjPoint_hom_ext
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_affineX
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_affineY
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_algebraMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_algebraMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_originW
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_originZ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_affineX
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_affineY
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_algebraMap
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_algebraMap
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_originW
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_originZ



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.SmoothLocusBaseChange
open GlobalTheory.WeierstrassCurve
namespace GlobalTheory.SmoothLocusBaseChange
theorem _root_.solution : ∀ (R R' : Type) [CommRing R] [CommRing R'] [IsDomain R'] [IsNoetherianRing R'] (f : R →+* R') (W : WeierstrassCurve R) (U : (GlobalTheory.WeierstrassCurve.scheme W).Opens), (∀ (k : Type) [Field k] (ρ : R →+* k) (P : Fin 3 → k) (h : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) P), ⊤ ≤ GlobalTheory.WeierstrassCurve.ptHom W ρ P h ⁻¹ᵁ U ↔ (W.map ρ).toProjective.Nonsingular P) → Smooth (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W) → GeometricallyIntegral (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W) → ∀ [GrpObj (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))], (∀ (k : Type) [Field k] (ρ : R →+* k) (x y : Over.mk (Spec.map (CommRingCat.ofHom ρ)) ⟶ (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))) (P Q : Fin 3 → k) (hP : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) P) (hQ : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) Q), x.left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ P hP → y.left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ Q hQ → ∃ h : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) ((W.map ρ).toProjective.add P Q), (lift x y ≫ μ[(Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))]).left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ _ h) → ∃ (U' : (GlobalTheory.WeierstrassCurve.scheme (W.map f)).Opens) (_ : GrpObj (Over.mk (U'.ι ≫ GlobalTheory.WeierstrassCurve.toSpec (W.map f)))) (e : (Over.mk (U'.ι ≫ GlobalTheory.WeierstrassCurve.toSpec (W.map f))) ≅ (Over.pullback (Spec.map (CommRingCat.ofHom f))).obj (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))), IsMonHom e.hom ∧ e.hom.left ≫ pullback.fst _ _ ≫ U.ι = U'.ι ≫ GlobalTheory.WeierstrassCurve.mapHom W f rfl ∧ (∀ (k : Type) [Field k] (ρ : R' →+* k) (P : Fin 3 → k) (h : GlobalTheory.WeierstrassCurve.IsUnimodularSol ((W.map f).map ρ) P), ⊤ ≤ GlobalTheory.WeierstrassCurve.ptHom (W.map f) ρ P h ⁻¹ᵁ U' ↔ ((W.map f).map ρ).toProjective.Nonsingular P) ∧ (∀ (k : Type) [Field k] (ρ : R' →+* k) (x y : Over.mk (Spec.map (CommRingCat.ofHom ρ)) ⟶ (Over.mk (U'.ι ≫ GlobalTheory.WeierstrassCurve.toSpec (W.map f)))) (P Q : Fin 3 → k) (hP : GlobalTheory.WeierstrassCurve.IsUnimodularSol ((W.map f).map ρ) P) (hQ : GlobalTheory.WeierstrassCurve.IsUnimodularSol ((W.map f).map ρ) Q), x.left ≫ U'.ι = GlobalTheory.WeierstrassCurve.ptHom (W.map f) ρ P hP → y.left ≫ U'.ι = GlobalTheory.WeierstrassCurve.ptHom (W.map f) ρ Q hQ → ∃ h : GlobalTheory.WeierstrassCurve.IsUnimodularSol ((W.map f).map ρ) (((W.map f).map ρ).toProjective.add P Q), (lift x y ≫ μ[(Over.mk (U'.ι ≫ GlobalTheory.WeierstrassCurve.toSpec (W.map f)))]).left ≫ U'.ι = GlobalTheory.WeierstrassCurve.ptHom (W.map f) ρ _ h) := by
  intro R R' _ _ _ _ f W U hU _ _ _ hmul
  let φ := Spec.map (CommRingCat.ofHom f)
  let U' : (scheme (W.map f)).Opens := mapHom W f rfl ⁻¹ᵁ U
  have hpb : IsPullback (mapHom W f rfl ∣_ U) (U'.ι ≫ toSpec (W.map f)) (U.ι ≫ toSpec W) φ :=
    (isPullback_morphismRestrict (mapHom W f rfl) U).paste_vert (isPullback_mapHom W f rfl)
  let e : Over.mk (U'.ι ≫ toSpec (W.map f)) ≅
      (Over.pullback φ).obj (Over.mk (U.ι ≫ toSpec W)) :=
    Over.isoMk hpb.isoPullback hpb.isoPullback_hom_snd
  have he : e.hom.left ≫ pullback.fst (U.ι ≫ toSpec W) φ = mapHom W f rfl ∣_ U :=
    hpb.isoPullback_hom_fst
  have he' : e.hom.left ≫ pullback.fst (U.ι ≫ toSpec W) φ ≫ U.ι = U'.ι ≫ mapHom W f rfl := by
    rw [← Category.assoc, he]
    exact morphismRestrict_ι _ _
  let : GrpObj (Over.mk (U'.ι ≫ toSpec (W.map f))) := GrpObj.ofIso e.symm
  have hinv : IsMonHom e.symm.hom := isMonHom_ofIso e.symm
  have hhom : IsMonHom e.hom := inferInstanceAs (IsMonHom e.symm.inv)
  refine ⟨U', inferInstance, e, hhom, he', ?_, ?_⟩
  · intro k _ ρ P h
    have := hU k (ρ.comp f) P (h.comp_of_map_eq rfl)
    rw [← ptHom_mapHom W f rfl ρ P h, Scheme.Hom.comp_preimage] at this
    exact this
  · intro k _ ρ x y P Q hP hQ hx hy
    have hw : ∀ z : Over.mk (Spec.map (CommRingCat.ofHom ρ)) ⟶
        Over.mk (U'.ι ≫ toSpec (W.map f)),
        (z.left ≫ e.hom.left ≫ pullback.fst (U.ι ≫ toSpec W) φ) ≫ U.ι ≫ toSpec W =
          Spec.map (CommRingCat.ofHom (ρ.comp f)) := by
      intro z
      have hz : z.left ≫ U'.ι ≫ toSpec (W.map f) = Spec.map (CommRingCat.ofHom ρ) := Over.w z
      rw [he, Category.assoc, hpb.w, ← Category.assoc]
      erw [hz]
      rw [CommRingCat.ofHom_comp, Spec.map_comp]
    have hι : ∀ z : Over.mk (Spec.map (CommRingCat.ofHom ρ)) ⟶
        Over.mk (U'.ι ≫ toSpec (W.map f)),
        (z.left ≫ e.hom.left ≫ pullback.fst (U.ι ≫ toSpec W) φ) ≫ U.ι =
          (z.left ≫ U'.ι) ≫ mapHom W f rfl := by
      intro z
      simp only [Category.assoc]
      erw [he']
    let a : Over.mk (Spec.map (CommRingCat.ofHom (ρ.comp f))) ⟶ Over.mk (U.ι ≫ toSpec W) :=
      Over.homMk _ (hw x)
    let b : Over.mk (Spec.map (CommRingCat.ofHom (ρ.comp f))) ⟶ Over.mk (U.ι ≫ toSpec W) :=
      Over.homMk _ (hw y)
    obtain ⟨h, hab⟩ := hmul k (ρ.comp f) a b P Q (hP.comp_of_map_eq rfl) (hQ.comp_of_map_eq rfl)
      ((hι x).trans (by rw [hx]; exact ptHom_mapHom W f rfl ρ P hP))
      ((hι y).trans (by rw [hy]; exact ptHom_mapHom W f rfl ρ Q hQ))
    refine ⟨h, ?_⟩
    have hl := lift_mul_hom_pullback_fst φ (Over.mk (U.ι ≫ toSpec W)) e.hom x y
      (Z₀ := Over.mk (Spec.map (CommRingCat.ofHom (ρ.comp f)))) (𝟙 _) a b
      (Category.id_comp _).symm (Category.id_comp _).symm
    apply (isPullback_mapHom W f rfl).hom_ext
    · refine (hι _).symm.trans ?_
      refine Eq.trans ?_ (hab.trans (ptHom_mapHom W f rfl ρ _ h).symm)
      rw [hl]
      erw [Category.id_comp]
      rfl
    · exact (Category.assoc _ _ _).trans ((Over.w
        (lift x y ≫ μ[Over.mk (U'.ι ≫ toSpec (W.map f))])).trans
        (ptHom_toSpec (W.map f) ρ _ h).symm)
end GlobalTheory.SmoothLocusBaseChange
