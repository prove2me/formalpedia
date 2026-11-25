-- Prove2me | solution 1 for GlobalTheory.HomExtension.exists_image_point_dvr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:22:22.639246+00:00
-- url     : https://prove2.me/submissions/dbf29282-8737-409a-a8c6-2f804138de10

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsMulEquivOfIsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MemPadicAlgClValuationSubringIffNormLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteOfIsClosedOfFiniteInterClosedPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SemiAbelianTorsionFiniteAndClosedPointFiniteOrde
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteResidueFieldIntegralClosurePadicInt
import Theorems.Thm_GlobalTheory_ExtUnique_pullback_map_left_fst
import Theorems.Thm_GlobalTheory_exists_mulEquiv_of_isGrpPullback
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_grpPullback_iso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_pullback


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
local notation "OO" p:max => (Valuation.valuationSubring (Valued.v : Valuation (PadicAlgCl p) NNReal))
local notation "cPt" p:max => (IsLocalRing.closedPoint (OO p) : Sp (OO p))
local notation "gPt" p:max => spMap (ValuationSubring.subtype (OO p))
open GlobalTheory
open GlobalTheory.HomExtension
namespace GlobalTheory.HomExtension
theorem _root_.solution
    (hext : ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K]
      [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'],
      IsSemiAbelian G → IsSemiAbelian G' →
      ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶
        (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f →
        ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f)
    {Z U : Scheme.{0}} (j : U ⟶ Z) {G G' : Over Z} [GrpObj G] [GrpObj G'] (hG : IsSemiAbelian G)
    (hG' : IsSemiAbelian G') (φ : (Over.pullback j).obj G ⟶ (Over.pullback j).obj G') [IsMonHom φ]
    (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] (a : Sp V ⟶ G.left) (a₀ : Sp K ⟶ pullback G.hom j)
    (ha : a₀ ≫ pullback.fst G.hom j = spMap (algebraMap V K) ≫ a) :
    ∃ b : Sp V ⟶ G'.left, b ≫ G'.hom = a ≫ G.hom ∧
      spMap (algebraMap V K) ≫ b = a₀ ≫ φ.left ≫ pullback.fst G'.hom j ∧
      ∀ (T : Scheme.{0}) (r : T ⟶ Sp V) (t : T ⟶ Z) (x : Over.mk t ⟶ G) (n : ℕ),
        x.left = r ≫ a → x ^ n = 1 → ∃ x' : Over.mk t ⟶ G', x'.left = r ≫ b ∧ x' ^ n = 1 := by
  let y : Sp V ⟶ Z := a ≫ G.hom
  let g : Sp K ⟶ Sp V := spMap (algebraMap V K)
  let y₀ : Sp K ⟶ U := a₀ ≫ pullback.snd G.hom j
  have hy : y₀ ≫ j = g ≫ y := by
    rw [Category.assoc, ← pullback.condition, reassoc_of% ha]
  obtain ⟨α, hα, hα'⟩ := grpPullback_iso
    ((isGrpPullback_pullback ((Over.pullback y).obj G) g).comp (isGrpPullback_pullback G y))
    (((isGrpPullback_pullback ((Over.pullback j).obj G) y₀).comp
      (isGrpPullback_pullback G j)).congr hy rfl)
  obtain ⟨β, hβ, hβ'⟩ := grpPullback_iso
    (((isGrpPullback_pullback ((Over.pullback j).obj G') y₀).comp
      (isGrpPullback_pullback G' j)).congr hy rfl)
    ((isGrpPullback_pullback ((Over.pullback y).obj G') g).comp (isGrpPullback_pullback G' y))
  obtain ⟨F, ⟨hF, hF'⟩, -⟩ := hext V K _ _ (IsSemiAbelian.pullback y G hG)
    (IsSemiAbelian.pullback y G' hG') (α.hom ≫ (Over.pullback y₀).map φ ≫ β.hom) inferInstance
  let a' : Sp V ⟶ pullback G.hom y := pullback.lift a (𝟙 _) (Category.id_comp _).symm
  have ha1 : a' ≫ pullback.fst G.hom y = a := pullback.lift_fst _ _ _
  have ha2 : a' ≫ pullback.snd G.hom y = 𝟙 _ := pullback.lift_snd _ _ _
  have hFw : F.left ≫ pullback.snd G'.hom y = pullback.snd G.hom y := Over.w F
  refine ⟨a' ≫ F.left ≫ pullback.fst G'.hom y, ?_, ?_, fun T r t x n hx hn => ?_⟩
  · rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% hFw, reassoc_of% ha2]
  · let c : Sp K ⟶ pullback (pullback.snd G.hom y) g :=
      pullback.lift (g ≫ a') (𝟙 _) (by rw [Category.assoc, ha2, Category.comp_id, Category.id_comp])
    have hc1 : c ≫ pullback.fst _ _ = g ≫ a' := pullback.lift_fst _ _ _
    have hc2 : c ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
    have h₁ := ExtUnique.pullback_map_left_fst g F
    have h₂ := ExtUnique.pullback_map_left_fst y₀ φ
    have hαw : α.hom.left ≫ pullback.snd (pullback.snd G.hom j) y₀ =
      pullback.snd (pullback.snd G.hom y) g := Over.w α.hom
    have h₃ : c ≫ α.hom.left ≫ pullback.fst (pullback.snd G.hom j) y₀ = a₀ := by
      apply pullback.hom_ext
      · erw [Category.assoc, Category.assoc, hα', reassoc_of% hc1, ha1, ha]
      · rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% hαw, reassoc_of% hc2]
    erw [hF'] at h₁
    rw [Over.comp_left, Over.comp_left] at h₁
    change g ≫ _ = _
    rw [← reassoc_of% hc1]
    erw [← reassoc_of% h₁, hβ', reassoc_of% h₂, reassoc_of% h₃]
  · have ht : t = r ≫ y := by
      rw [← Category.assoc, ← hx]; exact (Over.w x).symm
    obtain ⟨e, he⟩ := exists_mulEquiv_of_isGrpPullback (isGrpPullback_pullback G y) r t ht
    obtain ⟨e', he'⟩ := exists_mulEquiv_of_isGrpPullback (isGrpPullback_pullback G' y) r t ht
    have h₁ : (e.symm x).left = r ≫ a' := by
      apply pullback.hom_ext
      · erw [← he, e.apply_symm_apply, hx, Category.assoc, ha1]
      · rw [Category.assoc, ha2, Category.comp_id]; exact Over.w (e.symm x)
    refine ⟨e' (e.symm x ≫ F), ?_, ?_⟩
    · rw [he', Over.comp_left, h₁]; simp only [Category.assoc]
    · rw [← map_pow, ← MonObj.pow_comp, ← map_pow, hn, map_one, MonObj.one_comp, map_one]
end GlobalTheory.HomExtension
