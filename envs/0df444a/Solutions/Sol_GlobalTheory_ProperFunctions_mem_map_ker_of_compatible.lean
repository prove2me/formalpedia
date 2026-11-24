-- Prove2me | solution 1 for GlobalTheory.ProperFunctions.mem_map_ker_of_compatible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:14:10.410206+00:00
-- url     : https://prove2.me/submissions/d6af258e-ca46-41fd-80bd-f55874f297b3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Theorems.Thm_GlobalTheory_ProperFunctions_appLE_top_top
import Theorems.Thm_GlobalTheory_ProperFunctions_mem_map_ker_of_app_eq_zero
import Theorems.Thm_GlobalTheory_ProperFunctions_map_mem_map_of_comp_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TensorProduct Opposite
universe u
open GlobalTheory
open GlobalTheory.ProperFunctions
variable {X S : Scheme.{u}}
namespace GlobalTheory.ProperFunctions
theorem _root_.solution {Y T : Scheme.{u}} {f : T ⟶ S} {g : Y ⟶ X} {p : X ⟶ S}
    {q : Y ⟶ T} (H : IsPullback g q p f) [IsAffine S] [IsAffine T] [Flat p] (t : T)
    [Subsingleton T]
    (hq : Function.Surjective q.appTop) {e : S ⟶ X} (he : e ≫ p = 𝟙 S)
    (h : ∀ U : X.affineOpens, Γ(X, U.1))
    (hc : ∀ (U V : X.affineOpens) (hVU : V.1 ≤ U.1),
      X.presheaf.map (homOfLE hVU).op (h U) - h V ∈
        (RingHom.ker f.appTop.hom).map (p.appLE ⊤ V.1 (le_preimage_top p _)).hom)
    (hv : ∀ (U : X.affineOpens) (W : S.affineOpens) (hW : W.1 ≤ e ⁻¹ᵁ U.1),
      e.appLE U.1 W.1 hW (h U) ∈ (RingHom.ker f.appTop.hom).map
        (Scheme.Hom.appLE (𝟙 S) ⊤ W.1 (le_preimage_top _ _)).hom)
    (U : X.affineOpens) :
    h U ∈ (RingHom.ker f.appTop.hom).map (p.appLE ⊤ U.1 (le_preimage_top p _)).hom := by
  have hker : ∀ {B : CommRingCat.{u}} (χ : Γ(T, ⊤) ⟶ B),
      (RingHom.ker f.appTop.hom).map (f.appTop ≫ χ).hom = ⊥ := by
    intro B χ
    rw [CommRingCat.hom_comp, ← Ideal.map_map, (Ideal.map_eq_bot_iff_le_ker _).mpr le_rfl,
      Ideal.map_bot]

  have hres : ∀ (U V : X.affineOpens) (hVU : V.1 ≤ U.1),
      g.appLE U.1 (g ⁻¹ᵁ V.1) (g.preimage_mono hVU) (h U) = g.app V.1 (h V) := by
    intro U V hVU
    have e1 : p.appLE ⊤ V.1 (le_preimage_top p _) ≫ g.app V.1 =
        f.appTop ≫ q.appLE ⊤ (g ⁻¹ᵁ V.1) (le_preimage_top q _) := by
      rw [← appLE_top_top f (le_preimage_top f _), Scheme.Hom.app_eq_appLE,
        Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
      congr 1
      exact H.w
    have := map_mem_map_of_comp_eq e1 (hc U V hVU)
    rw [hker, Ideal.mem_bot, map_sub, sub_eq_zero, ← CommRingCat.comp_apply] at this
    rw [← this, Scheme.Hom.app_eq_appLE, Scheme.Hom.map_appLE]

  obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' (fun U : X.affineOpens ↦ g ⁻¹ᵁ U.1) ⊤
    (fun _ ↦ homOfLE le_top) (g.iSup_preimage_eq_top (iSup_affineOpens_eq_top X)).ge
    (fun U ↦ g.app U.1 (h U)) (by
      intro U U'
      refine Y.sheaf.eq_of_locally_eq'
        (fun V : {V : X.affineOpens // V.1 ≤ U.1 ⊓ U'.1} ↦ g ⁻¹ᵁ V.1.1) _
        (fun V ↦ homOfLE (g.preimage_mono V.2)) ?_ _ _ fun V ↦ ?_
      · intro y hy
        obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ :=
          X.isBasis_affineOpens.exists_subset_of_mem_open (a := g y) (u := (U.1 ⊓ U'.1 : X.Opens))
            hy (U.1 ⊓ U'.1).2
        exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, hVU⟩, hyV⟩
      · have h1 := hres U V.1 (V.2.trans inf_le_left)
        have h2 := hres U' V.1 (V.2.trans inf_le_right)
        have h3 := h1.trans h2.symm
        simp only [Scheme.Hom.appLE, CommRingCat.comp_apply] at h3
        change (Y.presheaf.map _ ≫ Y.presheaf.map _) _ = (Y.presheaf.map _ ≫ Y.presheaf.map _) _
        erw [← Functor.map_comp, ← Functor.map_comp]
        exact h3)
  obtain ⟨c, rfl⟩ := hq s

  let e' : T ⟶ Y := H.lift (f ≫ e) (𝟙 T) (by simp [he])
  have hc0 : c = 0 := by
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (e (f t))) isOpen_univ
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (a := f t) (u := (e ⁻¹ᵁ U : S.Opens))
        hxU (e ⁻¹ᵁ U).2
    have hT : (⊤ : T.Opens) ≤ f ⁻¹ᵁ W := fun t' _ ↦ by rwa [Subsingleton.elim t' t]
    have e1 : Scheme.Hom.appLE (𝟙 S) ⊤ W (le_preimage_top _ _) ≫ f.appLE W ⊤ hT =
        f.appTop ≫ 𝟙 _ := by
      rw [Scheme.Hom.appLE_comp_appLE, Category.comp_id, ← appLE_top_top f (le_preimage_top f _)]
      congr 1
    have h1 := map_mem_map_of_comp_eq e1 (hv ⟨U, hU⟩ ⟨W, hW⟩ hWU)
    rw [hker, Ideal.mem_bot, ← CommRingCat.comp_apply] at h1
    replace h1 := congr($(Scheme.Hom.appLE_comp_appLE f e U W ⊤ hWU hT) (h ⟨U, hU⟩)).symm.trans h1
    have hT' : (⊤ : T.Opens) ≤ e' ⁻¹ᵁ g ⁻¹ᵁ U := by
      rw [← Scheme.Hom.comp_preimage, H.lift_fst]
      exact hT.trans (f.preimage_mono hWU)
    have h2 := congr(e'.appLE (g ⁻¹ᵁ U) ⊤ hT' $(hs ⟨U, hU⟩))
    have e2 : g.app U ≫ e'.appLE (g ⁻¹ᵁ U) ⊤ hT' =
        (f ≫ e).appLE U ⊤ (hT.trans (f.preimage_mono hWU)) := by
      rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
      congr 1
      exact H.lift_fst ..
    have e3 : q.appTop ≫ Y.presheaf.map (homOfLE (le_top : g ⁻¹ᵁ U ≤ ⊤)).op ≫
        e'.appLE (g ⁻¹ᵁ U) ⊤ hT' = 𝟙 _ := by
      rw [Scheme.Hom.map_appLE, appLE_top_top, ← Scheme.Hom.comp_appTop, H.lift_snd,
        Scheme.Hom.id_appTop]
    have h3 := congr($e3 c)
    have h4 := congr($e2 (h ⟨U, hU⟩))
    simp only [CommRingCat.comp_apply, CommRingCat.id_apply] at h3 h4
    exact h3.symm.trans (h2.trans (h4.trans h1))
  refine mem_map_ker_of_app_eq_zero H U.2 _ ((hs U).symm.trans ?_)
  rw [hc0, map_zero]
  exact map_zero _
end GlobalTheory.ProperFunctions
