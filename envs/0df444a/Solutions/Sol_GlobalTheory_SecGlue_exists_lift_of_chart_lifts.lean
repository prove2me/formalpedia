-- Prove2me | solution 1 for GlobalTheory.SecGlue.exists_lift_of_chart_lifts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:46:22.948833+00:00
-- url     : https://prove2.me/submissions/015c5773-db62-4644-8f5d-f6b851ded6fd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpecHomExtOfLocalizationAwaySpanEqTopStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGlueSpecLocalizationAwayMorphismsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SquareZeroLocalLiftsCorrectedAgreeOnOverlapsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGlobalLiftOfChartLocalLiftsSquareZero
import Theorems.Thm_GlobalTheory_SecGlue_sqZeroInterp_apply
import Theorems.Thm_GlobalTheory_T_exists_glue_spec_localizationAway_morphisms
import Theorems.Thm_GlobalTheory_T_specHom_ext_of_localizationAway_span_eq_top
import Theorems.Thm_GlobalTheory_T_squareZero_local_lifts_corrected_agree_on_overlaps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SecGlue.sqZeroInterp_apply



set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SecGlue
namespace GlobalTheory.SecGlue
theorem _root_.solution : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ →
    ∀ (X : Over (Sp R)), Smooth X.hom → ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ (κ : Type) [Finite κ] (f : κ → R), Ideal.span (Set.range f) = ⊤ → ∀ V : κ → X.left.Opens, (∀ k, IsAffineOpen (V k)) →
    (∀ k, GlobalTheory.SecLift.LiftIn π X g₀ (f k) (V k)) → ∃ e : Sp R ⟶ X.left, e ≫ X.hom = 𝟙 _ ∧ spMap π ≫ e = g₀ := by
  intro R R₀ _ _ π hπ hI X hX g₀ hg₀ κ _ f hf V hV hL
  obtain ⟨e, he1, he2, he3⟩ := GlobalTheory.T.squareZero_local_lifts_corrected_agree_on_overlaps R R₀ π hπ hI X hX g₀ hg₀ κ f hf V hV hL
  obtain ⟨E, hE⟩ := GlobalTheory.T.exists_glue_spec_localizationAway_morphisms R κ f hf X.left e he3
  refine ⟨E, ?_, ?_⟩
  · refine GlobalTheory.T.specHom_ext_of_localizationAway_span_eq_top R κ f hf (Sp R) _ _ (fun k => ?_)
    rw [← Category.assoc, hE k, he1 k, Category.comp_id]
  · have hf₀ : Ideal.span (Set.range (fun k => π (f k))) = ⊤ := by
      rw [show (fun k => π (f k)) = π ∘ f from rfl, Set.range_comp, ← Ideal.map_span, hf, Ideal.map_top]
    refine GlobalTheory.T.specHom_ext_of_localizationAway_span_eq_top R₀ κ (fun k => π (f k)) hf₀ X.left _ _ (fun k => ?_)
    rw [← he2 k, ← hE k, ← Category.assoc, ← Category.assoc]
    congr 1
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact (IsLocalization.map_comp _).symm
end GlobalTheory.SecGlue
