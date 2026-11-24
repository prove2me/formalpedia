-- Prove2me | solution 1 for GlobalTheory.LevQuot.invariant_descends
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:19:34.394063+00:00
-- url     : https://prove2.me/submissions/ea1323fc-393a-4ec2-81c9-0ddb7e0b067e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAppTopEqOfEffectiveEpi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSubgroupOfFinite
import Theorems.Thm_GlobalTheory_LevQuot_isOpenImmersion_graph
import Theorems.Thm_GlobalTheory_LevQuot_appLE_congr_hom
import Theorems.Thm_GlobalTheory_LevQuot_exists_geomPoint
import Theorems.Thm_GlobalTheory_FlatDescent_existsUnique_app_eq_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry Opposite
open GlobalTheory GlobalTheory.LevQuot
variable {X Y : Scheme.{0}}
namespace GlobalTheory.LevQuot
theorem _root_.solution (r : X ⟶ Y) [Etale r] [QuasiCompact r] [Surjective r] {Γ : Type} (ρ : Γ → (X ⟶ X))
    (hρ : ∀ g, ρ g ≫ r = r)
    (htr : ∀ (k : Type) [Field k] [IsAlgClosed k] (y y' : Spec (CommRingCat.of k) ⟶ X), y ≫ r = y' ≫ r →
      ∃ g, y' = y ≫ ρ g) (V : Y.Opens) :
    Function.Injective (r.app V).hom ∧ ∀ f : Γ(X, r ⁻¹ᵁ V),
      (∀ g (h : r ⁻¹ᵁ V ≤ (ρ g) ⁻¹ᵁ (r ⁻¹ᵁ V)), ((ρ g).appLE _ _ h).hom f = f) → f ∈ Set.range (r.app V).hom := by
  have hcond : ∀ g, 𝟙 X ≫ r = ρ g ≫ r := fun g => by rw [Category.id_comp, hρ g]
  have hpb := IsPullback.of_hasPullback r r
  have hsame : ∀ x : ↥(pullback r r), r (pullback.snd r r x) = r (pullback.fst r r x) := fun x => by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  have hgW : pullback.fst r r ⁻¹ᵁ r ⁻¹ᵁ V ≤ pullback.snd r r ⁻¹ᵁ r ⁻¹ᵁ V := fun x hx => by
    change r (pullback.snd r r x) ∈ V
    rw [hsame]
    exact hx
  have hinvle : ∀ g, r ⁻¹ᵁ V ≤ (ρ g) ⁻¹ᵁ (r ⁻¹ᵁ V) := fun g y hy => by
    change r (ρ g y) ∈ V
    rw [← Scheme.Hom.comp_apply, hρ g]
    exact hy
  have key := fun s => GlobalTheory.FlatDescent.existsUnique_app_eq_iff r hpb V
    (pullback.fst r r ⁻¹ᵁ r ⁻¹ᵁ V) rfl le_rfl hgW s
  have hcompat : r.app V ≫ (pullback.fst r r).appLE _ _ le_rfl =
      r.app V ≫ (pullback.snd r r).appLE _ _ hgW :=
    (Scheme.Hom.comp_appLE _ _ _ _ _).symm.trans
      ((appLE_congr_hom pullback.condition _ _ _ _).trans (Scheme.Hom.comp_appLE _ _ _ _ _))
  constructor
  · intro a b hab
    obtain ⟨c, -, huniq⟩ := (key ((r.app V).hom a)).mpr (congrArg (fun φ => φ.hom a) hcompat)
    exact (huniq a rfl).trans (huniq b hab.symm).symm
  · intro f hinv
    refine ExistsUnique.exists ((key f).mpr ?_)
    apply TopCat.Presheaf.section_ext (pullback r r).sheaf
    intro x hx
    obtain ⟨k, _, _, w, pt, hw⟩ := exists_geomPoint (pullback r r) x
    obtain ⟨g, hg⟩ := htr k (w ≫ pullback.fst r r) (w ≫ pullback.snd r r)
      (by simp only [Category.assoc, pullback.condition])
    obtain ⟨ι, hιfst, hιsnd, hιop⟩ : ∃ ι : X ⟶ pullback r r,
        ι ≫ pullback.fst r r = 𝟙 X ∧ ι ≫ pullback.snd r r = ρ g ∧ IsOpenImmersion ι :=
      ⟨_, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, isOpenImmersion_graph r (ρ g) (hcond g)⟩
    have hwι : w = (w ≫ pullback.fst r r) ≫ ι := by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, hιfst, Category.comp_id]
      · rw [Category.assoc, Category.assoc, hιsnd, hg, Category.assoc]
    have hxι : x = ι ((w ≫ pullback.fst r r) pt) := by
      rw [← Scheme.Hom.comp_apply, ← hwι, hw]
    subst hxι
    have hfi : ∀ y, pullback.fst r r (ι y) = y := fun y => by
      rw [← Scheme.Hom.comp_apply, hιfst]
      rfl
    have hle : ι ⁻¹ᵁ (pullback.fst r r ⁻¹ᵁ r ⁻¹ᵁ V) ≤ r ⁻¹ᵁ V := fun y hy => by
      change r (pullback.fst r r (ι y)) ∈ V at hy
      rw [hfi] at hy
      exact hy
    have e1 : (pullback.fst r r).appLE (r ⁻¹ᵁ V) _ le_rfl ≫ ι.app _ =
        X.presheaf.map (homOfLE hle).op := by
      rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, appLE_congr_hom hιfst _ _ _ hle]
      dsimp only [Scheme.Hom.appLE]
      rw [Scheme.Hom.id_app]
      exact Category.id_comp _
    have e2 : (pullback.snd r r).appLE (r ⁻¹ᵁ V) _ hgW ≫ ι.app _ =
        (ρ g).appLE (r ⁻¹ᵁ V) (r ⁻¹ᵁ V) (hinvle g) ≫ X.presheaf.map (homOfLE hle).op := by
      rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE,
        appLE_congr_hom hιsnd _ _ _ (hle.trans (hinvle g)), Scheme.Hom.appLE_map]
    apply (ConcreteCategory.bijective_of_isIso (ι.stalkMap _)).1
    erw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.germ_stalkMap_apply]
    congr 1
    have h1 := congrArg (fun φ => φ.hom f) e1
    have h2 := congrArg (fun φ => φ.hom f) e2
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h1 h2
    rw [hinv g (hinvle g)] at h2
    exact h1.trans h2.symm
end GlobalTheory.LevQuot
