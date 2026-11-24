-- Prove2me | solution 1 for GlobalTheory.CechDR.FormExt.glue_one_forms
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:19:18.676751+00:00
-- url     : https://prove2.me/submissions/6dd40b3a-20bf-4b34-bbe7-99980819c454

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlueCommaOfBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasLocOAff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocalizationOfData
import Theorems.Thm_GlobalTheory_CechDR_FormExt_isUnit_mp_omExt_iff
import Theorems.Thm_GlobalTheory_CechDR_FormExt_hasLoc_omExt
import Theorems.Thm_GlobalTheory_CechDR_FormExt_span_inl_eq_top
import Theorems.Thm_GlobalTheory_CatCoh_Desc_glue_comma_of_basis
import Theorems.Thm_GlobalTheory_CechDR_hasLoc_OAff


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
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
  GlobalTheory.CatCoh GlobalTheory.CechDR
open GlobalTheory GlobalTheory.CechDR GlobalTheory.CechDR.FormExt
attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler
namespace GlobalTheory.CechDR.FormExt
theorem _root_.solution : ∀ {R' : Type} [CommRing R'] {X' : Scheme.{0}} (s' : X' ⟶ Sp R') {C' : Type} [Category.{0} C'], [Quiver.IsThin C'] → ∀ (G : C' ⥤ AffOp X'), (∀ T : AffOp X', ∃ (n : ℕ) (b : Fin n → (OAff s').obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X') (u : T ⟶ S), IsUnit (mp (OAff s') u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (t₁ t₂ : C') (S : AffOp X'), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → (OAff s').obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : AffOp X') (u : S ⟶ S'), IsUnit (mp (OAff s') u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → (∀ (T : AffOp X') (s : ∀ t, (T ⟶ G.obj t) → Ω[(OAff s').obj (G.obj t)⁄R']), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = p1 (OAff s') (G.map a) (s t u)) → ∃ ω : Ω[(OAff s').obj T⁄R'], ∀ t u, p1 (OAff s') u ω = s t u) := by
  intro R' _ X' s' C' _ _ G hcov hdir T s hs
  have unit : ∀ {S S' : AffOp X'} (u : S ⟶ S') (b : (OAff s').obj S),
      IsUnit (mp (omExt (OAff s')) u (TrivSqZeroExt.inl b)) → IsUnit (mp (OAff s') u b) :=
    fun u b h ↦ ((isUnit_mp_omExt_iff (OAff s') u _).1 h)
  obtain ⟨x, hx⟩ := GlobalTheory.CatCoh.Desc.glue_comma_of_basis (omExt (OAff s')) G (hasLoc_omExt (OAff s') (hasLoc_OAff s'))
    (fun T ↦ by
      obtain ⟨n, b, hb, h⟩ := hcov T
      exact ⟨n, fun i ↦ TrivSqZeroExt.inl (b i), span_inl_eq_top (OAff s') hb,
        fun i S u hu ↦ h i S u (unit u _ hu)⟩)
    (fun t₁ t₂ S a₁ a₂ ↦ by
      obtain ⟨n, b, hb, h⟩ := hdir t₁ t₂ S a₁ a₂
      exact ⟨n, fun i ↦ TrivSqZeroExt.inl (b i), span_inl_eq_top (OAff s') hb,
        fun i S' u hu ↦ h i S' u (unit u _ hu)⟩)
    T (fun t u ↦ TrivSqZeroExt.inr (s t u)) (fun t t' u a ↦ by
      apply TrivSqZeroExt.ext
      · exact (TrivSqZeroExt.fst_inr _ _).trans (((fst_extMap (OAff s') (G.map a) _).trans
          (by rw [TrivSqZeroExt.fst_inr, map_zero])).symm)
      · exact ((TrivSqZeroExt.snd_inr _ _).trans (hs t t' u a)).trans
          ((snd_extMap (OAff s') (G.map a) _).trans (by rw [TrivSqZeroExt.snd_inr])).symm)
  exact ⟨x.snd, fun t u ↦ (snd_extMap (OAff s') u x).symm.trans
    ((congrArg TrivSqZeroExt.snd (hx t u)).trans (TrivSqZeroExt.snd_inr _ _))⟩
end GlobalTheory.CechDR.FormExt
