-- Prove2me | solution 1 for GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.coboundary_on_piece
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:11:20.186876+00:00
-- url     : https://prove2.me/submissions/7d8be2d0-b3fe-404e-a535-9de8ce2f5f31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CovBy
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqZeroOfUpwardFamilyStandardCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGluedSectionUpwardFamilyStandardCoverStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OneCocycleUpwardFamilyIsCoboundaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TwoCocycleCoboundaryOnUnitLocusPiece
import Theorems.Thm_GlobalTheory_CatCoh_Desc_VandermondeTwoBasis_sep_of_covBy
import Theorems.Thm_GlobalTheory_CatCoh_Desc_coboundary_of_restrict
import Theorems.Thm_GlobalTheory_CatCoh_Desc_isUnit_comp
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_T_exists_glued_section_upwardFamily_standardCover
import Theorems.Thm_GlobalTheory_T_van1_of_covBy_upward_sieve
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm



set_option autoImplicit false
open CategoryTheory GlobalTheory.CatCoh
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.CatCoh.Desc GlobalTheory.CatCoh.Desc.VandermondeTwoBasis
open Classical
namespace GlobalTheory.CatCoh.Desc.VandermondeTwoBasis
theorem _root_.solution : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (T : C) (e : F.obj T) (p : C') (v : T ⟶ G.obj p), (∀ (S : C) (u : T ⟶ S), IsUnit (mp F u e) → Nonempty (G.obj p ⟶ S)) → ∀ (z : ∀ t t' t'', (T ⟶ G.obj t) → (t ⟶ t') → (t' ⟶ t'') → F.obj (G.obj t'')), (∀ t t' t'' t''' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t'') (c : t'' ⟶ t'''), mp F (G.map c) (z t t' t'' u a b) + z t t'' t''' u (a ≫ b) c = z t t' t''' u a (b ≫ c) + z t' t'' t''' (u ≫ G.map a) b c) → ∃ y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → F.obj (G.obj t'), ∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), IsUnit (mp F u e) → mp F (G.map b) (y t t' u a) - y t t'' u (a ≫ b) + y t' t'' (u ≫ G.map a) b = z t t' t'' u a b := by
  intro R _ C _ C' _ F G _ _ H hdir T e p v he z hz
  have cov : ∀ (t : C') (u : T ⟶ G.obj t), IsUnit (mp F u e) →
      CovBy F (fun S ↦ ∃ (t' : C') (_ : t ⟶ t'), Nonempty (p ⟶ t') ∧ Nonempty (G.obj t' ⟶ S))
        (G.obj t) := by
    intro t u hu
    obtain ⟨w⟩ := he _ u hu
    obtain ⟨n, b, hb, h⟩ := hdir t p (G.obj t) (𝟙 _) w
    refine ⟨n, b, hb, fun i S' u' hi ↦ ?_⟩
    obtain ⟨t₃, ⟨a⟩, h2, h3⟩ := h i S' u' hi
    exact ⟨t₃, a, h2, h3⟩
  have up : ∀ (t t' t'' : C') (_ : t ⟶ t') (_ : t' ⟶ t''), Nonempty (p ⟶ t') → Nonempty (p ⟶ t'') :=
    fun _ _ _ _ b ⟨α⟩ ↦ ⟨α ≫ b⟩
  exact coboundary_of_restrict (G ⋙ F) (E := fun t ↦ T ⟶ G.obj t) (fun u a ↦ u ≫ G.map a)
    (fun _ _ _ ↦ Subsingleton.elim _ _) (fun t u ↦ IsUnit (mp F u e))
    (fun t _ ↦ Nonempty (p ⟶ t)) (fun _ _ _ a h ↦ isUnit_comp (G.map a) h)
    (fun t u hu ↦ sep_of_covBy F G H hdir t (fun t' _ ↦ Nonempty (p ⟶ t')) (up t) (cov t u hu))
    (fun t u hu ↦ GlobalTheory.T.exists_glued_section_upwardFamily_standardCover F G H hdir t (fun t' _ ↦ Nonempty (p ⟶ t')) (up t) (cov t u hu))
    (fun t u hu ↦ GlobalTheory.T.van1_of_covBy_upward_sieve F G H hdir t (fun t' _ ↦ Nonempty (p ⟶ t')) (up t) (cov t u hu))
    z (fun t t' t'' t''' u a b c _ ↦ hz t t' t'' t''' u a b c)
    (fun t t' _ a ↦ if h : Nonempty (p ⟶ t) then z p t t' v h.some a else 0)
    (fun t t' t'' u a b hp ↦ by
      have hp' := up t t t' (𝟙 t) a hp
      simp only [dif_pos hp, dif_pos hp']
      have k := hz p t t' t'' v hp.some a b
      rw [Subsingleton.elim (v ≫ G.map hp.some) u,
        Subsingleton.elim (hp.some ≫ a) hp'.some] at k
      change mp F (G.map b) (z p t t' v hp.some a) - z p t t'' v hp.some (a ≫ b) +
        z p t' t'' v hp'.some b = z t t' t'' u a b
      linear_combination k)
end GlobalTheory.CatCoh.Desc.VandermondeTwoBasis
