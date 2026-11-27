-- Prove2me | solution 1 for GlobalTheory.sab_group_iso_of_generic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:41:11.839899+00:00
-- url     : https://prove2.me/submissions/e03fc0e6-bbf4-4c2c-acba-222c66d3e0a4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SabGroupIsoOfGeneric
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
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
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution
    (hx : ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K]
      [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' →
      ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G',
      IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f)
    (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (T K : Type) [CommRing T] [IsDomain T]
    [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (t t' : SAB H (Sp T)) (tK : SAB H (Sp K))
    (m : SABMap tK t (spMap (algebraMap T K))) (m' : SABMap tK t' (spMap (algebraMap T K))) :
    ∃ ψ : t.G ≅ t'.G, IsMonHom ψ.hom ∧ m.φ ≫ ψ.hom.left = m'.φ ∧
      ∀ a, t.act.act a ≫ ψ.hom = ψ.hom ≫ t'.act.act a := by
  have inj : ∀ (s s' : SAB H (Sp T)) (F F' : s.G ⟶ s'.G), IsMonHom F → IsMonHom F' →
      (Over.pullback (spMap (algebraMap T K))).map F = (Over.pullback (spMap (algebraMap T K))).map F' → F = F' := by
    intro s s' F F' hF hF' h
    exact (hx T K s.G s'.G s.semi s'.semi _ inferInstance).unique ⟨hF, rfl⟩ ⟨hF', h.symm⟩
  have A : ∀ {X Y : Over (Sp T)} (a : X ⟶ Y),
      ((Over.pullback (spMap (algebraMap T K))).map a).left ≫ pullback.fst Y.hom _ =
        pullback.fst X.hom _ ≫ a.left := fun a => pullback.lift_fst _ _ _
  obtain ⟨e, he, hφ⟩ := grpPullback_iso m.cart (isGrpPullback_pullback t.G _)
  obtain ⟨e', he', hφ'⟩ := grpPullback_iso m'.cart (isGrpPullback_pullback t'.G _)
  obtain ⟨F, ⟨hF, hFf⟩, -⟩ := hx T K t.G t'.G t.semi t'.semi (e.inv ≫ e'.hom) inferInstance
  obtain ⟨F', ⟨hF', hFf'⟩, -⟩ := hx T K t'.G t.G t'.semi t.semi (e'.inv ≫ e.hom) inferInstance
  have key : m.cm.F ≫ F.left = m'.cm.F := by
    rw [← hφ, Category.assoc, ← A, hFf, ← Category.assoc, ← Over.comp_left, e.hom_inv_id_assoc, hφ']
  refine ⟨⟨F, F', inj _ _ _ _ inferInstance inferInstance ?_, inj _ _ _ _ inferInstance inferInstance ?_⟩, hF, key,
    fun a => ?_⟩
  · rw [Functor.map_comp, hFf, hFf']; simp
  · rw [Functor.map_comp, hFf, hFf']; simp
  · show t.act.act a ≫ F = F ≫ t'.act.act a
    have := t.act.hom a
    have := t'.act.hom a
    refine inj _ _ _ _ inferInstance inferInstance ?_
    rw [← cancel_epi e.hom]
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simp only [Over.comp_left, Category.assoc, A]
      rw [reassoc_of% hφ, reassoc_of% hφ, ← reassoc_of% m.act a, reassoc_of% key, key, m'.act]
    · exact (Over.w _).trans (Over.w _).symm
end GlobalTheory
