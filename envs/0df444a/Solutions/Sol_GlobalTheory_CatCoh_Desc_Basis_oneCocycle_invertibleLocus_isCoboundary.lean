-- Prove2me | solution 1 for GlobalTheory.CatCoh.Desc.Basis.oneCocycle_invertibleLocus_isCoboundary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:20:42.506238+00:00
-- url     : https://prove2.me/submissions/b543e3b2-0deb-4817-9b44-46a17c60ac99

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocalizationOfData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitMpOmjExtIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CovBy
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OneCocycleCoboundaryCommaLocalBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlueCommaOfBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OneCocycleInvertibleLocusIsCoboundary
import Theorems.Thm_GlobalTheory_CatCoh_Desc_Basis_oneCocycle_coboundary_comma_localBasis
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm



set_option autoImplicit false
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.CatCoh.Desc GlobalTheory.CatCoh.Desc.Basis
namespace GlobalTheory.CatCoh.Desc.Basis
theorem _root_.solution : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ T : C, ∃ (n : ℕ) (b : Fin n → F.obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp F u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (T : C) (e : F.obj T) (y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → F.obj (G.obj t')), (∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), IsUnit (mp F u e) → y t t'' u (a ≫ b) = mp F (G.map b) (y t t' u a) + y t' t'' (u ≫ G.map a) b) → ∃ g : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t), ∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), IsUnit (mp F u e) → g t' (u ≫ G.map a) - mp F (G.map a) (g t u) = y t t' u a := by
  intro R _ C _ C' _ F G _ _ H hcov hdir T e y hy
  obtain ⟨L, l, hl, -, -, huniv⟩ := H T e
  have hunit : ∀ t (w : L ⟶ G.obj t), IsUnit (mp F (l ≫ w) e) := by
    intro t w
    rw [mp_comp]
    exact hl.map _
  obtain ⟨gL, hgL⟩ := oneCocycle_coboundary_comma_localBasis F G H hcov hdir L (fun t t' w a ↦ y t t' (l ≫ w) a)
    (fun t t' t'' w a b ↦ by
      have h := hy t t' t'' (l ≫ w) a b (hunit t w)
      rw [Category.assoc] at h
      exact h)
  classical
  refine ⟨fun t u ↦ if h : ∃ w : L ⟶ G.obj t, l ≫ w = u then gL t h.choose else 0, ?_⟩
  have hg : ∀ t (u : T ⟶ G.obj t) (w : L ⟶ G.obj t), l ≫ w = u →
      (if h : ∃ w : L ⟶ G.obj t, l ≫ w = u then gL t h.choose else 0) = gL t w := by
    intro t u w hw
    have h : ∃ w : L ⟶ G.obj t, l ≫ w = u := ⟨w, hw⟩
    rw [dif_pos h]
    exact congrArg (gL t) (Subsingleton.elim _ _)
  intro t t' u a hu
  obtain ⟨w, hw, -⟩ := huniv (G.obj t) u hu
  have hw' : l ≫ (w ≫ G.map a) = u ≫ G.map a := by rw [← Category.assoc, hw]
  simp only []
  rw [hg t u w hw, hg t' (u ≫ G.map a) (w ≫ G.map a) hw', hgL t t' w a, hw]
end GlobalTheory.CatCoh.Desc.Basis
