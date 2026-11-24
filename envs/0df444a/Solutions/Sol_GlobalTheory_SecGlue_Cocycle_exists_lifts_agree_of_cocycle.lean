-- Prove2me | solution 1 for GlobalTheory.SecGlue.Cocycle.exists_lifts_agree_of_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:06:16.227068+00:00
-- url     : https://prove2.me/submissions/a2e00f18-3415-45b3-801b-3df2b50478dc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationIndependentOfChartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineCombinationSquareZeroLiftsChartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartSpecMapComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpecHomExtOfLocalizationAwaySpanEqTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLiftsAgreeOfCocycle
import Theorems.Thm_GlobalTheory_SecGlue_Cocycle_spMap_comp_spMap
import Theorems.Thm_GlobalTheory_SecGlue_Cocycle_awayMap_surjective
import Theorems.Thm_GlobalTheory_SecGlue_Cocycle_ker_awayMap_sq
import Theorems.Thm_GlobalTheory_SecGlue_Cocycle_isCombIn_restrict_chart
import Theorems.Thm_GlobalTheory_SecGlue_Cocycle_eq_of_cocycle
import Theorems.Thm_GlobalTheory_SecGlue_hom_ext_of_span_eq_top
import Theorems.Thm_GlobalTheory_T_exists_affineCombination_squareZero_lifts_chart


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.SecGlue GlobalTheory.SecGlue.Cocycle
namespace GlobalTheory.SecGlue.Cocycle
theorem _root_.solution : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ →
    ∀ (X : Over (Sp R)), ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ (κ : Type) [Fintype κ] (f : κ → R), Ideal.span (Set.range f) = ⊤ → ∀ (V : κ → X.left.Opens), (∀ k, IsAffineOpen (V k)) →
    ∀ (e : ∀ k, Sp (Localization.Away (f k)) ⟶ X.left),
    (∀ k, e k ≫ X.hom = spMap (algebraMap R (Localization.Away (f k)))) →
    (∀ k, spMap (Localization.awayMap π (f k)) ≫ e k = spMap (algebraMap R₀ (Localization.Away (π (f k)))) ≫ g₀) →
    (∀ k, e k ⁻¹ᵁ V k = ⊤) →
    ∀ (N : ℕ) (t : κ → ∀ j, Sp (Localization.Away (f j)) ⟶ X.left),
    (∀ k j, t k j ≫ X.hom = spMap (algebraMap R (Localization.Away (f j)))) →
    (∀ k j, spMap (Localization.awayMap π (f j)) ≫ t k j = spMap (algebraMap R₀ (Localization.Away (π (f j)))) ≫ g₀) →
    (∀ k j, t k j ⁻¹ᵁ V j = ⊤) →
    ∀ (n : κ → κ → ℕ) (s : ∀ j l, Fin (n j l) → Localization.Away (f j * f l)) (W : ∀ j l, Fin (n j l) → X.left.Opens),
    (∀ j l, Ideal.span (Set.range (s j l)) = ⊤) → (∀ j l i, IsAffineOpen (W j l i)) →
    (∀ j l i, (spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f l)) (f j) (f l)) ≫ e j) ⁻¹ᵁ W j l i = ⊤) →
    (∀ j l k i, GlobalTheory.SecGlue.IsCombIn (W j l i) (spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (f j * f l)) (f l) (f j)) ≫ e l)
        (spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f l)) (f j) (f l)) ≫ t k j)
        ![spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (f j * f l)) (f l) (f j)) ≫ t k l, spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f l)) (f j) (f l)) ≫ e j]
        ![1, 1 - algebraMap R (Localization.Away (s j l i)) (f k) ^ (N)]) →
    ∃ e : ∀ k, Sp (Localization.Away (f k)) ⟶ X.left,
      (∀ k, e k ≫ X.hom = spMap (algebraMap R (Localization.Away (f k)))) ∧
      (∀ k, spMap (Localization.awayMap π (f k)) ≫ e k = spMap (algebraMap R₀ (Localization.Away (π (f k)))) ≫ g₀) ∧
      ∀ j k, spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f k)) (f j) (f k)) ≫ e j =
        spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (f j * f k)) (f k) (f j)) ≫ e k := by
  intro R R₀ _ _ π hπ h2 X g₀ hg₀ κ _ f hf V hV e he he₀ heV N t ht ht₀ htV n s W hs hW heW hco
  have hpow : Ideal.span (Set.range fun k => f k ^ N) = ⊤ := by
    have := Ideal.span_pow_eq_top _ hf N
    rwa [← Set.range_comp] at this
  obtain ⟨a, ha⟩ : ∃ a : κ → R, ∑ k, a k * f k ^ N = 1 :=
    Ideal.mem_span_range_iff_exists_fun.1 (hpow ▸ Submodule.mem_top)
  have hte : ∀ j k, spMap (Localization.awayMap π (f j)) ≫ t k j =
      spMap (Localization.awayMap π (f j)) ≫ e j := fun j k => (ht₀ k j).trans (he₀ j).symm
  choose c hc hc₀ hcp using fun j => GlobalTheory.T.exists_affineCombination_squareZero_lifts_chart X.left (V j) (hV j) _ _
    (Localization.awayMap π (f j)) (awayMap_surjective π hπ _) (ker_awayMap_sq π h2 _) κ (e j)
    (fun k => t k j) (fun k => algebraMap R _ (a k)) (heV j) (hte j)
  refine ⟨c, fun j => (hcp j R X.hom fun k => (ht k j).trans (he j).symm).trans (he j),
    fun j => (hc₀ j).trans (he₀ j), fun j l => ?_⟩
  refine hom_ext_of_span_eq_top _ _ (s j l) (hs j l) _ _ _ fun i => ?_
  obtain ⟨hlW, -⟩ := hco j l j i
  have hjW := heW j l i
  rw [← Category.assoc, spMap_comp_spMap] at hlW hjW
  have h₁ := isCombIn_restrict_chart (hV j) (hW j l i) _ (awayMap_surjective π hπ _)
    (ker_awayMap_sq π h2 _) _ _ _ _ _ (hte j) (hc j) hjW
  have h₂ := isCombIn_restrict_chart (hV l) (hW j l i) _ (awayMap_surjective π hπ _)
    (ker_awayMap_sq π h2 _) _ _ _ _ _ (hte l) (hc l) hlW
  simp only [RingHom.comp_apply, IsLocalization.Away.awayToAwayRight_eq,
    IsLocalization.Away.awayToAwayLeft_eq, ← IsScalarTower.algebraMap_apply,
    ← spMap_comp_spMap, Category.assoc] at h₁ h₂
  refine eq_of_cocycle (hW j l i) _ _ _ _ _ _ _
    (fun k => algebraMap R (Localization.Away (s j l i)) (f k) ^ N) ?_ h₁ h₂ fun k => hco j l k i
  simp only [← map_pow, ← map_mul, ← map_sum, ha, map_one]
end GlobalTheory.SecGlue.Cocycle
