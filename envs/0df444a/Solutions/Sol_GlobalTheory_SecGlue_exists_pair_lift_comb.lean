-- Prove2me | solution 1 for GlobalTheory.SecGlue.exists_pair_lift_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:21:12.664888+00:00
-- url     : https://prove2.me/submissions/d999e848-b25c-4db2-a59c-77cc24bc1e2d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartSpecMapComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreimageEqOfSquareZeroThickeningStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSqZeroExtendLocalizationAwayPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSquareZeroLiftBasicOpenPairAgree
import Theorems.Thm_P2M_GlobalTheory_SecGlue_Pair_spMap_comp__c0415674e1cb
import Theorems.Thm_GlobalTheory_SecGlue_Pair_chart_rebuild
import Theorems.Thm_GlobalTheory_SecGlue_Pair_fromSpec_comp_top
import Theorems.Thm_GlobalTheory_SecGlue_Pair_chartHom_fromSpec
import Theorems.Thm_GlobalTheory_SecGlue_Pair_chartHom_congr
import Theorems.Thm_GlobalTheory_SecGlue_Pair_fromSpec_over
import Theorems.Thm_GlobalTheory_SecGlue_Pair_chartHom_comp_strHom
import Theorems.Thm_GlobalTheory_SecGlue_Pair_smooth_strHom
import Theorems.Thm_GlobalTheory_SecGlue_Pair_awayMap_surjective
import Theorems.Thm_GlobalTheory_SecGlue_Pair_ker_awayMap
import Theorems.Thm_GlobalTheory_SecGlue_Pair_ker_awayMap_sq
import Theorems.Thm_GlobalTheory_SecGlue_Pair_red_comp
import Theorems.Thm_GlobalTheory_SecGlue_Pair_equiv_restrict
import Theorems.Thm_GlobalTheory_SecGlue_Pair_exists_awayEquiv
import Theorems.Thm_GlobalTheory_SecGlue_Pair_comp_over
import Theorems.Thm_GlobalTheory_SecGlue_chartHom_spMap_comp
import Theorems.Thm_GlobalTheory_SecGlue_preimage_spMap_comp_eq_top
import Theorems.Thm_GlobalTheory_SecGlue_sqZeroInterp_apply
import Theorems.Thm_GlobalTheory_T_exists_sqZero_extend_localizationAway_pow
import Theorems.Thm_GlobalTheory_T_preimage_eq_of_square_zero_thickening
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
noncomputable section
open GlobalTheory GlobalTheory.SecGlue
open GlobalTheory.SecGlue.Pair
set_option maxHeartbeats 1000000
namespace GlobalTheory.SecGlue
theorem _root_.solution : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ →
    ∀ (X : Over (Sp R)), Smooth X.hom → ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ (a b : R) (V : X.left.Opens), IsAffineOpen V →
    ∀ (ea : Sp (Localization.Away a) ⟶ X.left), ea ≫ X.hom = spMap (algebraMap R (Localization.Away a)) →
      spMap (Localization.awayMap π a) ≫ ea = spMap (algebraMap R₀ (Localization.Away (π a))) ≫ g₀ → ea ⁻¹ᵁ V = ⊤ →
    ∀ (eb : Sp (Localization.Away b) ⟶ X.left), eb ≫ X.hom = spMap (algebraMap R (Localization.Away b)) →
      spMap (Localization.awayMap π b) ≫ eb = spMap (algebraMap R₀ (Localization.Away (π b))) ≫ g₀ →
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ t : Sp (Localization.Away a) ⟶ X.left,
      t ≫ X.hom = spMap (algebraMap R (Localization.Away a)) ∧
      spMap (Localization.awayMap π a) ≫ t = spMap (algebraMap R₀ (Localization.Away (π a))) ≫ g₀ ∧ t ⁻¹ᵁ V = ⊤ ∧
      GlobalTheory.SecGlue.IsCombIn V
        (spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (a * b)) a b) ≫ ea)
        (spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (a * b)) a b) ≫ t)
        ![spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (a * b)) b a) ≫ eb]
        ![algebraMap R (Localization.Away (a * b)) b ^ N] := by
  intro R R₀ _ _ π hπ hsq X hX g₀ hg₀ a b V hV ea hea hea₀ heaV eb heb heb₀
  haveI := hX
  letI : Algebra R Γ(X.left, V) := (strHom X V).toAlgebra
  haveI : Algebra.Smooth R Γ(X.left, V) := smooth_strHom X hV

  have hρ : (IsLocalization.Away.awayToAwayRight (S := Localization.Away a) (P := Localization.Away (a * b))
      a b).comp (algebraMap R (Localization.Away a)) = algebraMap R (Localization.Away (a * b)) :=
    RingHom.ext (IsLocalization.Away.awayToAwayRight_eq a b)
  have hρ' : (IsLocalization.Away.awayToAwayLeft (S := Localization.Away b) (P := Localization.Away (a * b))
      b a).comp (algebraMap R (Localization.Away b)) = algebraMap R (Localization.Away (a * b)) :=
    RingHom.ext (IsLocalization.Away.awayToAwayLeft_eq b a)
  generalize IsLocalization.Away.awayToAwayRight (S := Localization.Away a) (P := Localization.Away (a * b))
      a b = ρ at hρ ⊢
  generalize IsLocalization.Away.awayToAwayLeft (S := Localization.Away b) (P := Localization.Away (a * b))
      b a = ρ' at hρ' ⊢
  have hred : spMap (Localization.awayMap π (a * b)) ≫ spMap ρ' ≫ eb =
      spMap (Localization.awayMap π (a * b)) ≫ spMap ρ ≫ ea :=
    (red_comp π g₀ b (a * b) (dvd_mul_left b a) eb heb₀ ρ' hρ').trans
      (red_comp π g₀ a (a * b) (dvd_mul_right a b) ea hea₀ ρ hρ).symm
  have h2 : (spMap ρ ≫ ea) ⁻¹ᵁ V = ⊤ := preimage_spMap_comp_eq_top ρ heaV
  have hbV : (spMap ρ' ≫ eb) ⁻¹ᵁ V = ⊤ :=
    (GlobalTheory.T.preimage_eq_of_square_zero_thickening (Localization.Away (a * b)) (Localization.Away (π (a * b))) (Localization.awayMap π (a * b))
      (awayMap_surjective π hπ _) (ker_awayMap_sq π hsq _) X.left (spMap ρ' ≫ eb) (spMap ρ ≫ ea) hred V).trans h2

  let φ : Γ(X.left, V) →ₐ[R] Localization.Away a :=
    { chartHom V ea heaV with
      commutes' := fun r => RingHom.congr_fun (chartHom_comp_strHom X hV _ ea heaV hea) r }

  obtain ⟨eP⟩ := exists_awayEquiv a b
  have hePc : (eP.toAlgHom : Localization.Away (a * b) →+* Localization.Away (algebraMap R (Localization.Away a) b)).comp
      (algebraMap R (Localization.Away (a * b))) = algebraMap R (Localization.Away (algebraMap R (Localization.Away a) b)) :=
    eP.toAlgHom.comp_algebraMap
  have heP := equiv_restrict a b eP ρ hρ
  have heb' : (spMap ρ' ≫ eb) ≫ X.hom = spMap (algebraMap R (Localization.Away (a * b))) :=
    comp_over eb X.hom _ heb ρ' _ hρ'
  let ψ : Γ(X.left, V) →ₐ[R] Localization.Away (algebraMap R (Localization.Away a) b) :=
    { (eP : Localization.Away (a * b) →+* Localization.Away (algebraMap R (Localization.Away a) b)).comp (chartHom V (spMap ρ' ≫ eb) hbV) with
      commutes' := fun r => by
        show eP (chartHom V (spMap ρ' ≫ eb) hbV (strHom X V r)) = _
        rw [← RingHom.comp_apply, chartHom_comp_strHom X hV _ _ hbV heb', AlgEquiv.commutes] }
  have hJ : RingHom.ker (Localization.awayMap π a) ^ 2 = ⊥ := ker_awayMap_sq π hsq a
  have hcond : ∀ x, ψ x - algebraMap (Localization.Away a) (Localization.Away (algebraMap R (Localization.Away a) b)) (φ x) ∈
      (RingHom.ker (Localization.awayMap π a)).map (algebraMap (Localization.Away a) (Localization.Away (algebraMap R (Localization.Away a) b))) := by
    intro x
    have hd : chartHom V (spMap ρ' ≫ eb) hbV x - chartHom V (spMap ρ ≫ ea) h2 x ∈
        RingHom.ker (Localization.awayMap π (a * b)) := by
      rw [RingHom.mem_ker, map_sub, sub_eq_zero,
        ← chartHom_spMap_comp V _ _ hbV (preimage_spMap_comp_eq_top _ hbV),
        ← chartHom_spMap_comp V _ _ h2 (preimage_spMap_comp_eq_top _ h2)]
      exact RingHom.congr_fun (chartHom_congr V hred _ _) x
    rw [ker_awayMap] at hd
    have h3 := Ideal.mem_map_of_mem (eP : Localization.Away (a * b) →+* Localization.Away (algebraMap R (Localization.Away a) b)) hd
    rw [Ideal.map_map, show (eP : Localization.Away (a * b) →+* Localization.Away (algebraMap R (Localization.Away a) b)).comp
        (algebraMap R (Localization.Away (a * b))) = algebraMap R (Localization.Away (algebraMap R (Localization.Away a) b)) from
        RingHom.ext fun r => eP.commutes r, map_sub] at h3
    rw [ker_awayMap, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
    have e2 : algebraMap (Localization.Away a) (Localization.Away (algebraMap R (Localization.Away a) b)) (φ x) =
        eP (chartHom V (spMap ρ ≫ ea) h2 x) := by
      rw [chartHom_spMap_comp V ρ ea heaV h2 x, heP]
      rfl
    rw [e2]
    exact h3
  obtain ⟨N₀, hN⟩ := GlobalTheory.T.exists_sqZero_extend_localizationAway_pow R Γ(X.left, V) (Localization.Away a) (RingHom.ker (Localization.awayMap π a)) hJ (algebraMap R (Localization.Away a) b) φ ψ hcond
  refine ⟨N₀, fun N hN' => ?_⟩
  obtain ⟨χ, hχJ, hχ⟩ := hN N hN'
  have htop := fromSpec_comp_top hV (χ : Γ(X.left, V) →+* Localization.Away a)
  refine ⟨spMap (χ : Γ(X.left, V) →+* Localization.Away a) ≫ hV.fromSpec, ?_, ?_, htop, ?_⟩
  · rw [Category.assoc, fromSpec_over, ← spMap_comp']
    exact congrArg spMap (RingHom.ext fun r => χ.commutes r)
  · rw [← hea₀, ← chart_rebuild hV ea heaV, ← Category.assoc, ← Category.assoc, ← spMap_comp',
      ← spMap_comp']
    refine congrArg (fun f => spMap f ≫ hV.fromSpec) (RingHom.ext fun x => ?_)
    have := hχJ x
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at this
    exact this
  · refine ⟨h2, preimage_spMap_comp_eq_top ρ htop, fun i => by rw [Matrix.cons_val_fin_one]; exact hbV, fun x => ?_⟩
    simp only [Fin.sum_univ_one, Matrix.cons_val_zero]
    rw [chartHom_spMap_comp V ρ _ htop, chartHom_fromSpec hV _ htop, chartHom_spMap_comp V ρ ea heaV]
    apply eP.injective
    rw [map_add, map_mul, map_sub, map_pow, heP, heP, AlgEquiv.commutes,
      IsScalarTower.algebraMap_apply R (Localization.Away a) (Localization.Away (algebraMap R (Localization.Away a) b))]
    exact hχ x
end GlobalTheory.SecGlue
