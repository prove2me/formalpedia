-- Prove2me | solution 1 for GlobalTheory.CatCoh.Desc.Basis.eq_zero_of_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:19:44.495113+00:00
-- url     : https://prove2.me/submissions/2c965464-acf1-4cbf-a40c-b6a0efd15eab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OneCocycleCoboundaryCommaLocalBasis
import Theorems.Thm_GlobalTheory_CatCoh_Desc_sep_std


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.CatCoh.Desc GlobalTheory.CatCoh.Desc.Basis
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C']
namespace GlobalTheory.CatCoh.Desc.Basis
theorem _root_.solution (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) (H : HasLoc F)
    (hdir : (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) →
        ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')))
    {t₁ t₂ : C'} {S : C} (h₁ : Nonempty (G.obj t₁ ⟶ S)) (h₂ : Nonempty (G.obj t₂ ⟶ S)) (z : F.obj S)
    (hz : ∀ t (S' : C) (ψ : S ⟶ S'), Nonempty (t₁ ⟶ t) → Nonempty (t₂ ⟶ t) →
      Nonempty (G.obj t ⟶ S') → mp F ψ z = 0) : z = 0 := by
  obtain ⟨w₁⟩ := h₁
  obtain ⟨w₂⟩ := h₂
  obtain ⟨n, b, hb, h⟩ := hdir t₁ t₂ S w₁ w₂
  exact sep_std H hb z fun S' ψ ⟨i, hi⟩ ↦ by
    obtain ⟨t₃, h1, h2, h3⟩ := h i S' ψ hi
    exact hz t₃ S' ψ h1 h2 h3
end GlobalTheory.CatCoh.Desc.Basis
