-- Prove2me | solution 1 for GlobalTheory.SecGlue.exists_pow_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:02:32.285384+00:00
-- url     : https://prove2.me/submissions/36bbcb6a-cf58-49cc-8c58-e06090241e53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AwayMapEqOfRed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartSpecMapComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationIndependentOfChartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineCombinationSquareZeroLiftsChartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartSpecMapCompStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreimageEqOfSquareZeroThickeningStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AlgHomEqMulPowOfEqLocalizationAwayStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPowCocycle
import Theorems.Thm_GlobalTheory_SecGlue_Red_awR_comp
import Theorems.Thm_GlobalTheory_SecGlue_Red_awL_comp
import Theorems.Thm_GlobalTheory_SecGlue_Red_exists_comb_pow
import Theorems.Thm_GlobalTheory_SecGlue_Red_affineCombination_squareZero_lifts_cocycle
import Theorems.Thm_GlobalTheory_SecGlue_Red_IsRed_eq
import Theorems.Thm_GlobalTheory_SecGlue_Red_awayMap_eq_of_red
import Theorems.Thm_GlobalTheory_SecGlue_Red_isRed_self
import Theorems.Thm_GlobalTheory_SecGlue_Red_ker_mk_sq
import Theorems.Thm_GlobalTheory_SecGlue_Red_spMap_comp
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
open GlobalTheory.SecGlue GlobalTheory.SecGlue.Red IsLocalization.Away
namespace GlobalTheory.SecGlue
theorem _root_.solution : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ →
    ∀ (X : Over (Sp R)), Smooth X.hom → ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ (κ : Type) [Fintype κ] (f : κ → R), ∀ (V : κ → X.left.Opens), (∀ k, IsAffineOpen (V k)) →
    ∀ (e : ∀ k, Sp (Localization.Away (f k)) ⟶ X.left),
    (∀ k, e k ≫ X.hom = spMap (algebraMap R (Localization.Away (f k)))) →
    (∀ k, spMap (Localization.awayMap π (f k)) ≫ e k = spMap (algebraMap R₀ (Localization.Away (π (f k)))) ≫ g₀) →
    (∀ k, e k ⁻¹ᵁ V k = ⊤) →
    ∀ (N : ℕ) (t : κ → ∀ j, Sp (Localization.Away (f j)) ⟶ X.left),
    (∀ k j, t k j ≫ X.hom = spMap (algebraMap R (Localization.Away (f j)))) →
    (∀ k j, spMap (Localization.awayMap π (f j)) ≫ t k j = spMap (algebraMap R₀ (Localization.Away (π (f j)))) ≫ g₀) →
    (∀ k j, t k j ⁻¹ᵁ V j = ⊤) →
    (∀ k j, GlobalTheory.SecGlue.IsCombIn (V j) (spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f k)) (f j) (f k)) ≫ e j) (spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f k)) (f j) (f k)) ≫ t k j)
        ![spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (f j * f k)) (f k) (f j)) ≫ e k] ![algebraMap R (Localization.Away (f j * f k)) (f k) ^ N]) →
    ∀ (n : κ → κ → ℕ) (s : ∀ j l, Fin (n j l) → Localization.Away (f j * f l)) (W : ∀ j l, Fin (n j l) → X.left.Opens),
    (∀ j l, Ideal.span (Set.range (s j l)) = ⊤) → (∀ j l i, IsAffineOpen (W j l i)) →
    (∀ j l i, (spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f l)) (f j) (f l)) ≫ e j) ⁻¹ᵁ W j l i = ⊤) →
    ∃ (M : ℕ) (t' : κ → ∀ j, Sp (Localization.Away (f j)) ⟶ X.left),
      (∀ k j, t' k j ≫ X.hom = spMap (algebraMap R (Localization.Away (f j)))) ∧
      (∀ k j, spMap (Localization.awayMap π (f j)) ≫ t' k j = spMap (algebraMap R₀ (Localization.Away (π (f j)))) ≫ g₀) ∧
      (∀ k j, t' k j ⁻¹ᵁ V j = ⊤) ∧
      ∀ j l k i, GlobalTheory.SecGlue.IsCombIn (W j l i) (spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (f j * f l)) (f l) (f j)) ≫ e l)
        (spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f l)) (f j) (f l)) ≫ t' k j)
        ![spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (f j * f l)) (f l) (f j)) ≫ t' k l, spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f l)) (f j) (f l)) ≫ e j]
        ![1, 1 - algebraMap R (Localization.Away (s j l i)) (f k) ^ (N + M)] := by
  intro R R₀ _ _ π hπ hsq X hsm g₀ _hg₀ κ _ f V hV e he hered hev N t ht htred htv hcomb n s W hs hW hej
  let ρR : ∀ j l (i : Fin (n j l)), Localization.Away (f j) →+* Localization.Away (s j l i) :=
    fun j l i => (algebraMap (Localization.Away (f j * f l)) _).comp
      (awayToAwayRight (P := Localization.Away (f j * f l)) (f j) (f l))
  let ρL : ∀ j l (i : Fin (n j l)), Localization.Away (f l) →+* Localization.Away (s j l i) :=
    fun j l i => (algebraMap (Localization.Away (f j * f l)) _).comp
      (awayToAwayLeft (P := Localization.Away (f j * f l)) (f l) (f j))
  have hρR : ∀ j l i, (ρR j l i).comp (algebraMap R _) = algebraMap R _ := fun j l i => by
    simp only [ρR]; rw [RingHom.comp_assoc, awR_comp, ← IsScalarTower.algebraMap_eq]
  have hρL : ∀ j l i, (ρL j l i).comp (algebraMap R _) = algebraMap R _ := fun j l i => by
    simp only [ρL]; rw [RingHom.comp_assoc, awL_comp, ← IsScalarTower.algebraMap_eq]
  have hA : ∀ j l i, (spMap (ρR j l i) ≫ e j) ⁻¹ᵁ W j l i = ⊤ := fun j l i => by
    have := hej j l i
    rwa [← Category.assoc, ← spMap_comp] at this
  have hQ := fun j l k (i : Fin (n j l)) => exists_comb_pow π hπ hsq X hsm g₀ (f j) (f l) (f k)
    (V j) (V l) (W j l i) (hV j) (hV l) (hW j l i) (e j) (t k j) (e l) (t k l) (e k) (he j) (ht k j)
    (he l) (ht k l) (hered j) (htred k j) (hered l) (htred k l) (hered k) N (hcomb k j) (hcomb k l)
    _ (ρR j l i) (ρL j l i) (hρR j l i) (hρL j l i) (hA j l i)
  choose c hc M₀ hM₀ using hQ
  let M := Finset.univ.sup (fun p : (j : κ) × (l : κ) × κ × Fin (n j l) =>
    M₀ p.1 p.2.1 p.2.2.1 p.2.2.2)
  have hMle : ∀ j l k i, M₀ j l k i ≤ M := fun j l k i =>
    Finset.le_sup (f := fun p : (j : κ) × (l : κ) × κ × Fin (n j l) =>
      M₀ p.1 p.2.1 p.2.2.1 p.2.2.2) (Finset.mem_univ ⟨j, l, k, i⟩)
  have hT := fun k j => GlobalTheory.T.exists_affineCombination_squareZero_lifts_chart X.left (V j) (hV j) (Localization.Away (f j)) _
    (Ideal.Quotient.mk (redI π (Localization.Away (f j)))) Ideal.Quotient.mk_surjective
    (ker_mk_sq π hsq _) (Fin 1) (e j) ![t k j] ![algebraMap R (Localization.Away (f j)) (f k) ^ M]
    (hev j) (Fin.forall_fin_one.2 ((isRed_self π hπ g₀ (f j) (t k j) (htred k j)).eq
      (isRed_self π hπ g₀ (f j) (e j) (hered j))))
  choose t' ht'c ht'q ht'R using hT
  refine ⟨M, t', fun k j => ?_, fun k j => ?_, fun k j => (ht'c k j).2.1, fun j l k i => ?_⟩
  · exact (ht'R k j R X.hom (Fin.forall_fin_one.2 ((ht k j).trans (he j).symm))).trans (he j)
  · exact (awayMap_eq_of_red π (f j) _ _ (ht'q k j)).trans (hered j)
  · have h := affineCombination_squareZero_lifts_cocycle π hπ hsq X g₀ (f j) (f l) (f k) (V j) (V l) (W j l i) (hV j) (hV l) (hW j l i)
      (e j) (t k j) (t' k j) (e l) (t k l) (t' k l) (hered j) (htred k j) (hered l) (htred k l)
      N M (M₀ j l k i) (hMle j l k i) (ht'c k j) (ht'c k l) _ (ρR j l i) (ρL j l i) (hρR j l i)
      (hρL j l i) (hA j l i) (c j l k i) (hc j l k i) (hM₀ j l k i)
    simpa only [ρR, ρL, spMap_comp, Category.assoc] using h
end GlobalTheory.SecGlue
