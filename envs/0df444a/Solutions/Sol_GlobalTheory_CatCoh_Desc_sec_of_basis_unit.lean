-- Prove2me | solution 1 for GlobalTheory.CatCoh.Desc.sec_of_basis_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:14:22.05283+00:00
-- url     : https://prove2.me/submissions/1d0396a9-8301-4cff-a900-3ccf6406df0d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocalizationOfData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitMpOmjExtIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CovBy
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OneCocycleCoboundaryCommaLocalBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlueCommaOfBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SectionsInvertibleLocusOfBasisFunctor
import Theorems.Thm_GlobalTheory_CatCoh_Desc_glue_comma_of_basis
import Theorems.Thm_GlobalTheory_CatCoh_Desc_isUnit_comp
import Theorems.Thm_GlobalTheory_CatCoh_Desc_sep_std


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR
set_option autoImplicit false
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.CatCoh.Desc
namespace GlobalTheory.CatCoh.Desc
theorem _root_.solution : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ T : C, ∃ (n : ℕ) (b : Fin n → F.obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp F u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (T : C) (e : F.obj T) (s : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t)), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), IsUnit (mp F u e) → s t' (u ≫ G.map a) = mp F (G.map a) (s t u)) → ∃ x : ∀ S, (T ⟶ S) → F.obj S, Desc.IsSec F (fun S u ↦ IsUnit (mp F u e)) x ∧ ∀ t (u : T ⟶ G.obj t), IsUnit (mp F u e) → x (G.obj t) u = s t u := by
  intro R _ C _ C' _ F G _ _ H hcov hdir T e s hs
  have uniq : ∀ (S : C) (y : F.obj S), (∀ t (w : S ⟶ G.obj t), mp F w y = 0) → y = 0 := by
    intro S y hy
    obtain ⟨n, b, hb, hb'⟩ := hcov S
    refine sep_std H hb y fun S'' u' ⟨i, hi⟩ ↦ ?_
    obtain ⟨t, v, w, rfl⟩ := hb' i S'' u' hi
    rw [mp_comp, hy t v, map_zero]
  have hex : ∀ S (u : T ⟶ S), ∃ y : F.obj S, IsUnit (mp F u e) →
      ∀ t (w : S ⟶ G.obj t), mp F w y = s t (u ≫ w) := by
    intro S u
    by_cases h : IsUnit (mp F u e)
    · obtain ⟨y, hy⟩ := glue_comma_of_basis F G H hcov hdir S (fun t w ↦ s t (u ≫ w))
        fun t t' w a ↦ by
          rw [← Category.assoc]
          exact hs t t' (u ≫ w) a (isUnit_comp w h)
      exact ⟨y, fun _ ↦ hy⟩
    · exact ⟨0, fun h' ↦ absurd h' h⟩
  choose x hx using hex
  refine ⟨x, fun S S' u ψ hu ↦ sub_eq_zero.1 (uniq S' _ fun t w ↦ ?_), fun t u hu ↦ ?_⟩
  · rw [map_sub, hx S' (u ≫ ψ) (isUnit_comp ψ hu) t w, ← mp_comp, hx S u hu t (ψ ≫ w),
      Category.assoc, sub_self]
  · have := hx (G.obj t) u hu t (𝟙 _)
    rwa [mp_id, Category.comp_id] at this
end GlobalTheory.CatCoh.Desc
