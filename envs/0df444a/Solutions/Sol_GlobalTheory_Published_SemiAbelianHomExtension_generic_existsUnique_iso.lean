-- Prove2me | solution 1 for GlobalTheory.Published.SemiAbelianHomExtension.generic_existsUnique_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:08:25.87428+00:00
-- url     : https://prove2.me/submissions/3eea46bb-283b-4902-8985-cd2a158213dd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_SemiabelianTori_GeometricallyConnectedSplitTorusAff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GenericExistsUniqueOActOfIsGrpPullback
import Theorems.Thm_GlobalTheory_Published_SemiAbelianHomExtension_generic_existsUnique_iso_of_isGrpPullback
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
universe u
namespace GlobalTheory.StalkLimit
open TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
variable {S X : Scheme.{u}} (x : S) (p : X ⟶ S)
variable {x p} {X' : Scheme.{u}} {φ : X' ⟶ X} {p' : X' ⟶ Spec (S.presheaf.stalk x)}
end GlobalTheory.StalkLimit
namespace GlobalTheory
open ExtUnique
namespace IsGenericPointHom
variable {U S : Scheme.{u}} [IsIntegral S] {j : U ⟶ S}
private theorem isGrpPullback_pullback_fst {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G] :
    IsGrpPullback ((Over.pullback f).obj G) G f (pullback.fst G.hom f) := by
  refine ⟨IsPullback.of_hasPullback _ _, ?_⟩
  intro T x y x₀ y₀ hx hy
  have e : ∀ {A B : Over S} (g : A ⟶ B),
      ((Over.pullback f).map g).left ≫ pullback.fst B.hom f = pullback.fst A.hom f ≫ g.left := by
    intro A B g
    simp only [Over.pullback_map_left]
    exact pullback.lift_fst _ _ _
  have key : (lift x₀ y₀).left =
      (lift x y ≫ Functor.LaxMonoidal.μ (Over.pullback f) G G).left ≫ pullback.fst (G ⊗ G).hom f := by
    apply pullback.hom_ext
    · calc (lift x₀ y₀).left ≫ pullback.fst G.hom G.hom = (lift x₀ y₀ ≫ fst G G).left := rfl
        _ = x.left ≫ pullback.fst G.hom f := by rw [lift_fst, hx]
        _ = (lift x y ≫ Functor.LaxMonoidal.μ (Over.pullback f) G G ≫ (Over.pullback f).map (fst G G)).left ≫
              pullback.fst G.hom f := by
          rw [Functor.Monoidal.μ_fst, lift_fst]
        _ = _ := by simp only [Over.comp_left, Category.assoc, e]; rfl
    · calc (lift x₀ y₀).left ≫ pullback.snd G.hom G.hom = (lift x₀ y₀ ≫ snd G G).left := rfl
        _ = y.left ≫ pullback.fst G.hom f := by rw [lift_snd, hy]
        _ = (lift x y ≫ Functor.LaxMonoidal.μ (Over.pullback f) G G ≫ (Over.pullback f).map (snd G G)).left ≫
              pullback.fst G.hom f := by
          rw [Functor.Monoidal.μ_snd, lift_snd]
        _ = _ := by simp only [Over.comp_left, Category.assoc, e]; rfl
  change (lift x₀ y₀ ≫ μ).left =
    (lift x y ≫ (Functor.LaxMonoidal.μ (Over.pullback f) G G ≫ (Over.pullback f).map μ)).left ≫ pullback.fst G.hom f
  rw [Over.comp_left, key]
  simp only [Over.comp_left, Category.assoc, e]
end IsGenericPointHom
end GlobalTheory
namespace GlobalTheory.Published.SemiAbelianHomExtension
open ExtUnique
variable {S U : Scheme.{0}} [IsIntegral S] [AlgebraicGeometry.IsNoetherian S] {j : U ⟶ S}
private theorem pullback_map_eq_iff_fst_comp {S₀ U₀ : Scheme.{0}} {t : U₀ ⟶ S₀} {G₀ H₀ : Over S₀} (F : G₀ ⟶ H₀)
    (f : (Over.pullback t).obj G₀ ⟶ (Over.pullback t).obj H₀) :
    (Over.pullback t).map F = f ↔ f.left ≫ pullback.fst H₀.hom t = pullback.fst G₀.hom t ≫ F.left := by
  constructor
  · rintro rfl
    simp only [Over.pullback_map_left]
    exact pullback.lift_fst _ _ _
  · intro hF
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simp only [Over.pullback_map_left, pullback.lift_fst]
      exact hF.symm
    · simp only [Over.pullback_map_left, pullback.lift_snd]
      exact (Over.w f).symm
end GlobalTheory.Published.SemiAbelianHomExtension
end
end

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
universe u
open GlobalTheory GlobalTheory.Published GlobalTheory.Published.SemiAbelianHomExtension
open ExtUnique
variable {S U : Scheme.{0}} [IsIntegral S] [AlgebraicGeometry.IsNoetherian S] {j : U ⟶ S}
namespace GlobalTheory.Published.SemiAbelianHomExtension
theorem _root_.solution (h : SemiAbelianHomExtension) (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S)
    (hj : IsGenericPointHom j) {G H : Over S} [GrpObj G] [GrpObj H]
    (hG : IsSemiAbelian G) (hH : IsSemiAbelian H) (e : (Over.pullback j).obj G ≅ (Over.pullback j).obj H)
    [IsMonHom e.hom] : ∃! E : G ≅ H, IsMonHom E.hom ∧ (Over.pullback j).map E.hom = e.hom := by
  obtain ⟨E, ⟨hE, cE⟩, u⟩ := generic_existsUnique_iso_of_isGrpPullback h hS hj hG hH
    (IsGenericPointHom.isGrpPullback_pullback_fst j G) (IsGenericPointHom.isGrpPullback_pullback_fst j H) e
  exact ⟨E, ⟨hE, (pullback_map_eq_iff_fst_comp E.hom e.hom).2 cE⟩,
    fun E' ⟨hE', c⟩ => u E' ⟨hE', (pullback_map_eq_iff_fst_comp E'.hom e.hom).1 c⟩⟩
end GlobalTheory.Published.SemiAbelianHomExtension
