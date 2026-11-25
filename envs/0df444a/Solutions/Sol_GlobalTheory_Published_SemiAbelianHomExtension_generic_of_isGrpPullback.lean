-- Prove2me | solution 1 for GlobalTheory.Published.SemiAbelianHomExtension.generic_of_isGrpPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:00:17.045701+00:00
-- url     : https://prove2.me/submissions/c37763cd-5752-4950-9a05-65bcb6ac5163

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_SemiabelianTori_GeometricallyConnectedSplitTorusAff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GenericExistsUniqueOActOfIsGrpPullback
import Theorems.Thm_GlobalTheory_IsGenericPointHom_quasiCompact_and_dominant
import Theorems.Thm_GlobalTheory_spread_hom_generic_of_isGrpPullback
import Theorems.Thm_GlobalTheory_Published_SemiAbelianHomExtension_quasiCompact_and_dominant
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans

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
private lemma hom_ext_lemma {W X Y Z : Scheme.{u}} {f g : X ⟶ Y} (s : Y ⟶ Z) [IsSeparated s]
    (hs : f ≫ s = g ≫ s) (w : W ⟶ X) [IsSchemeTheoreticallyDominant w] (hw : w ≫ f = w ≫ g) : f = g := by
  let e := pullback.fst (pullback.lift f g hs) (pullback.diagonal s)
  let k : W ⟶ pullback (pullback.lift f g hs) (pullback.diagonal s) :=
    pullback.lift w (w ≫ f) (by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.diagonal_fst, Category.comp_id]
      · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.diagonal_snd, Category.comp_id, hw])
  have hk : k ≫ e = w := pullback.lift_fst _ _ _
  have hker : e.ker = ⊥ := by
    refine le_bot_iff.mp ((Scheme.Hom.le_ker_comp k e).trans ?_)
    rw [hk, w.ker_eq_bot]
  have : IsIso e := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hker
  have hc := pullback.condition (f := pullback.lift f g hs) (g := pullback.diagonal s)
  have h₁ : e ≫ f = pullback.snd _ _ := by
    calc e ≫ f = e ≫ pullback.lift f g hs ≫ pullback.fst s s := by rw [pullback.lift_fst]
      _ = pullback.snd _ _ ≫ pullback.diagonal s ≫ pullback.fst s s := by rw [reassoc_of% hc]
      _ = pullback.snd _ _ := by simp
  have h₂ : e ≫ g = pullback.snd _ _ := by
    calc e ≫ g = e ≫ pullback.lift f g hs ≫ pullback.snd s s := by rw [pullback.lift_snd]
      _ = pullback.snd _ _ ≫ pullback.diagonal s ≫ pullback.snd s s := by rw [reassoc_of% hc]
      _ = pullback.snd _ _ := by simp
  exact (cancel_epi e).mp (h₁.trans h₂.symm)
end IsGenericPointHom
end GlobalTheory
namespace GlobalTheory.Published.SemiAbelianHomExtension
open ExtUnique
variable {S U : Scheme.{0}} [IsIntegral S] [AlgebraicGeometry.IsNoetherian S] {j : U ⟶ S}
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
    (hj : IsGenericPointHom j) {G H : Over S} [GrpObj G] [GrpObj H] (hG : IsSemiAbelian G) (hH : IsSemiAbelian H)
    {G' H' : Over U} [GrpObj G'] [GrpObj H'] {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left}
    (hφ : IsGrpPullback G' G j φ) (hψ : IsGrpPullback H' H j ψ) (f : G' ⟶ H') [IsMonHom f] :
    ∃! F : G ⟶ H, IsMonHom F ∧ f.left ≫ ψ = φ ≫ F.left := by
  have _ : Smooth G.hom := hG.smooth
  have _ : IsSeparated G.hom := hG.separated
  have _ : QuasiCompact G.hom := hG.quasiCompact
  have _ : Smooth H.hom := hH.smooth
  have _ : IsSeparated H.hom := hH.separated
  obtain ⟨V, hηV, -, g, hg, w, hw₁, hw₂⟩ := spread_hom_generic_of_isGrpPullback hj hφ hψ f
  have hVd : Dense (V : Set S) := V.isOpen.dense ⟨_, hηV⟩
  obtain ⟨F, ⟨hF, hFg⟩, -⟩ := h S hS V hVd G H hG hH g hg
  have hsq : ((Over.pullback V.ι).map F).left ≫ pullback.fst H.hom V.ι = pullback.fst G.hom V.ι ≫ F.left := by
    simp only [Over.pullback_map_left]
    exact pullback.lift_fst _ _ _
  have hex : f.left ≫ ψ = φ ≫ F.left := by
    rw [← hw₂, ← hFg, hsq, ← Category.assoc, hw₁]
  refine ⟨F, ⟨hF, hex⟩, ?_⟩
  rintro F₂ ⟨-, hF₂⟩
  obtain ⟨_, _⟩ := hj.quasiCompact_and_dominant
  have hpb : IsPullback G'.hom φ j G.hom := hφ.1.flip
  have _ : IsSchemeTheoreticallyDominant φ := IsSchemeTheoreticallyDominant.of_isPullback hpb
  apply Over.OverMorphism.ext
  exact IsGenericPointHom.hom_ext_lemma H.hom (by rw [Over.w, Over.w]) φ (hF₂.symm.trans hex)
end GlobalTheory.Published.SemiAbelianHomExtension
