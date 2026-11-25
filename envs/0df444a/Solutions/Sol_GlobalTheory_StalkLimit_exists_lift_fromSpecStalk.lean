-- Prove2me | solution 1 for GlobalTheory.StalkLimit.exists_lift_fromSpecStalk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:25:13.628945+00:00
-- url     : https://prove2.me/submissions/b54794e9-27f6-4af5-b736-ec636acdb4c2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_SemiabelianTori_GeometricallyConnectedSplitTorusAff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GenericExistsUniqueOActOfIsGrpPullback

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
universe u
open GlobalTheory GlobalTheory.StalkLimit
open TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.StalkLimit
theorem _root_.solution {S T : Scheme.{u}} (x : S) (t : T ⟶ S)
    (ht : ∀ V : S.Opens, x ∈ V → ⊤ ≤ t ⁻¹ᵁ V) :
    ∃ l : T ⟶ Spec (S.presheaf.stalk x), l ≫ S.fromSpecStalk x = t := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ x) isOpen_univ
  have hU' : IsAffineOpen U := hU
  have htop : (⊤ : T.Opens) ≤ t ⁻¹ᵁ U := ht U hxU
  have unit_of_top : ∀ s : Γ(T, ⊤), T.basicOpen s = ⊤ → IsUnit s := by
    intro s hs
    have h1 := (T.toRingedSpace.isUnit_res_basicOpen s).map (T.presheaf.map (homOfLE hs.ge).op).hom
    convert h1 using 1
    change s = (T.presheaf.map _ ≫ T.presheaf.map _).hom s
    rw [← Functor.map_comp, Subsingleton.elim (_ ≫ _) (𝟙 _), CategoryTheory.Functor.map_id]
    rfl
  let _ := (S.presheaf.germ U x hxU).hom.toAlgebra
  have := hU'.isLocalization_stalk ⟨x, hxU⟩
  have hunit : ∀ y : (hU'.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl,
      IsUnit ((t.appLE U ⊤ htop).hom y) := by
    intro y
    have h1 : IsUnit (S.presheaf.germ U x hxU y) := IsLocalization.map_units (S.presheaf.stalk x) y
    have h2 : x ∈ S.basicOpen (y : Γ(S, U)) := (S.mem_basicOpen' (U := U) (y : Γ(S, U)) ⟨x, hxU⟩).mpr h1
    apply unit_of_top
    rw [Scheme.basicOpen_appLE]
    exact top_le_iff.mp (le_inf le_rfl (ht _ h2))
  let χ := IsLocalization.lift (M := (hU'.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl)
    (S := S.presheaf.stalk x) (g := (t.appLE U ⊤ htop).hom) hunit
  have hχ : S.presheaf.germ U x hxU ≫ CommRingCat.ofHom χ = t.appLE U ⊤ htop := by
    ext1
    exact IsLocalization.lift_comp _
  refine ⟨T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom χ), ?_⟩
  have hfac : T.toSpecΓ ≫ Spec.map (t.appLE U ⊤ htop) ≫ hU'.fromSpec = t := by
    have e1 := Scheme.Opens.toSpecΓ_SpecMap_appLE t U ⊤ htop
    rw [Scheme.Opens.toSpecΓ_top, Category.assoc] at e1
    have : IsIso (⊤ : T.Opens).ι := isIso_of_isOpenImmersion_of_opensRange_eq_top _ (by simp)
    rw [← cancel_epi (⊤ : T.Opens).ι, reassoc_of% e1, hU'.toSpecΓ_fromSpec,
      Scheme.Hom.resLE_comp_ι]
  rw [← hU'.fromSpecStalk_eq_fromSpecStalk hxU, IsAffineOpen.fromSpecStalk, Category.assoc,
    ← Spec.map_comp_assoc, hχ, hfac]
end GlobalTheory.StalkLimit
