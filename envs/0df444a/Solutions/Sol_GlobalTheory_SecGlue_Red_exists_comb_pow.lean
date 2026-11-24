-- Prove2me | solution 1 for GlobalTheory.SecGlue.Red.exists_comb_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:53:08.734527+00:00
-- url     : https://prove2.me/submissions/b3cc28bf-b2d8-464c-9b2c-08263ac9e5e9

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
import Theorems.Thm_GlobalTheory_SecGlue_Red_chartHom_pow_mul_eq
import Theorems.Thm_GlobalTheory_SecGlue_Red_isCombIn_congr
import Theorems.Thm_GlobalTheory_SecGlue_Red_isCombIn_one
import Theorems.Thm_GlobalTheory_SecGlue_Red_isCombIn_two
import Theorems.Thm_GlobalTheory_SecGlue_Red_comp_overR
import Theorems.Thm_GlobalTheory_SecGlue_Red_awR_comp
import Theorems.Thm_GlobalTheory_SecGlue_Red_awL_comp
import Theorems.Thm_GlobalTheory_SecGlue_CombEx_chartHom_spMap_comp
import Theorems.Thm_GlobalTheory_SecGlue_Red_IsRed_eq
import Theorems.Thm_GlobalTheory_SecGlue_Red_away_ext
import Theorems.Thm_GlobalTheory_SecGlue_Red_isRed_comp
import Theorems.Thm_GlobalTheory_SecGlue_Red_isRed_of_away
import Theorems.Thm_GlobalTheory_SecGlue_Red_isUnit_of_away
import Theorems.Thm_GlobalTheory_SecGlue_Red_ker_mk_sq
import Theorems.Thm_GlobalTheory_SecGlue_Red_spMap_comp
import Theorems.Thm_GlobalTheory_SecGlue_chartHom_spMap_comp
import Theorems.Thm_GlobalTheory_SecGlue_preimage_spMap_comp_eq_top
import Theorems.Thm_GlobalTheory_T_exists_affineCombination_squareZero_lifts_chart
import Theorems.Thm_GlobalTheory_T_isAffineCombinationInChart_specMap_comp
import Theorems.Thm_GlobalTheory_T_isAffineCombination_independent_of_chart
import Theorems.Thm_GlobalTheory_T_preimage_eq_of_square_zero_thickening


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
open GlobalTheory GlobalTheory.SecGlue GlobalTheory.SecGlue.Red
open IsLocalization.Away
namespace GlobalTheory.SecGlue.Red
theorem _root_.solution {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀)
    (hπ : Function.Surjective π) (hsq : RingHom.ker π ^ 2 = ⊥) (X : Over (Sp R)) (hsm : Smooth X.hom)
    (g₀ : Sp R₀ ⟶ X.left) (fj fl fk : R) (Vj Vl W : X.left.Opens) (hVj : IsAffineOpen Vj)
    (hVl : IsAffineOpen Vl) (hW : IsAffineOpen W)
    (ej tj : Sp (Localization.Away fj) ⟶ X.left) (el tl : Sp (Localization.Away fl) ⟶ X.left)
    (ek : Sp (Localization.Away fk) ⟶ X.left)
    (hej : ej ≫ X.hom = spMap (algebraMap R _)) (htj : tj ≫ X.hom = spMap (algebraMap R _))
    (hel : el ≫ X.hom = spMap (algebraMap R _)) (htl : tl ≫ X.hom = spMap (algebraMap R _))
    (rej : spMap (Localization.awayMap π fj) ≫ ej = spMap (algebraMap R₀ (Localization.Away (π fj))) ≫ g₀)
    (rtj : spMap (Localization.awayMap π fj) ≫ tj = spMap (algebraMap R₀ (Localization.Away (π fj))) ≫ g₀)
    (rel : spMap (Localization.awayMap π fl) ≫ el = spMap (algebraMap R₀ (Localization.Away (π fl))) ≫ g₀)
    (rtl : spMap (Localization.awayMap π fl) ≫ tl = spMap (algebraMap R₀ (Localization.Away (π fl))) ≫ g₀)
    (rek : spMap (Localization.awayMap π fk) ≫ ek = spMap (algebraMap R₀ (Localization.Away (π fk))) ≫ g₀)
    (N : ℕ)
    (hcj : IsCombIn Vj (spMap (awayToAwayRight (P := Localization.Away (fj * fk)) fj fk) ≫ ej)
      (spMap (awayToAwayRight (P := Localization.Away (fj * fk)) fj fk) ≫ tj)
      ![spMap (awayToAwayLeft (P := Localization.Away (fj * fk)) fk fj) ≫ ek]
      ![algebraMap R (Localization.Away (fj * fk)) fk ^ N])
    (hcl : IsCombIn Vl (spMap (awayToAwayRight (P := Localization.Away (fl * fk)) fl fk) ≫ el)
      (spMap (awayToAwayRight (P := Localization.Away (fl * fk)) fl fk) ≫ tl)
      ![spMap (awayToAwayLeft (P := Localization.Away (fl * fk)) fk fl) ≫ ek]
      ![algebraMap R (Localization.Away (fl * fk)) fk ^ N])
    (S : Type) [CommRing S] [Algebra R S] (ρj : Localization.Away fj →+* S)
    (ρl : Localization.Away fl →+* S) (hρj : ρj.comp (algebraMap R _) = algebraMap R S)
    (hρl : ρl.comp (algebraMap R _) = algebraMap R S) (hA : (spMap ρj ≫ ej) ⁻¹ᵁ W = ⊤) :
    ∃ c : Sp S ⟶ X.left, IsCombIn W (spMap ρl ≫ el) c ![spMap ρl ≫ tl, spMap ρj ≫ ej]
        ![1, 1 - algebraMap R S fk ^ N] ∧
      ∃ M₀ : ℕ, ∀ (h₁ : (spMap ρj ≫ tj) ⁻¹ᵁ W = ⊤) (h₂ : c ⁻¹ᵁ W = ⊤) x,
        algebraMap R S fk ^ M₀ * chartHom W (spMap ρj ≫ tj) h₁ x =
          algebraMap R S fk ^ M₀ * chartHom W c h₂ x := by
  set fS := algebraMap R S fk with hfS
  let ι : S →+* Localization.Away fS := algebraMap S (Localization.Away fS)
  have hι : ι.comp (algebraMap R S) = algebraMap R (Localization.Away fS) :=
    (IsScalarTower.algebraMap_eq R S _).symm

  have rA := isRed_of_away π hπ g₀ fj ej rej S ρj hρj
  have rTJ := isRed_of_away π hπ g₀ fj tj rtj S ρj hρj
  have rEL := isRed_of_away π hπ g₀ fl el rel S ρl hρl
  have rTL := isRed_of_away π hπ g₀ fl tl rtl S ρl hρl
  have hq := Ideal.Quotient.mk_surjective (I := redI π S)
  have hq2 := ker_mk_sq π hsq S
  have land : ∀ u, IsRed π hπ g₀ S u → u ⁻¹ᵁ W = ⊤ := fun u hu =>
    (GlobalTheory.T.preimage_eq_of_square_zero_thickening S _ _ hq hq2 X.left u _ (hu.eq rA) W).trans hA

  obtain ⟨c, hc, -, hcR⟩ := GlobalTheory.T.exists_affineCombination_squareZero_lifts_chart X.left W hW S _ _ hq hq2 (Fin 2) (spMap ρl ≫ el)
    ![spMap ρl ≫ tl, spMap ρj ≫ ej] ![1, 1 - fS ^ N] (land _ rEL)
    (Fin.forall_fin_two.2 ⟨rTL.eq rEL, rA.eq rEL⟩)
  have oEL := comp_overR X fl ρl hρl el hel
  have hcX : c ≫ X.hom = spMap (algebraMap R S) := by
    rw [hcR R X.hom (Fin.forall_fin_two.2 ⟨(comp_overR X fl ρl hρl tl htl).trans oEL.symm,
      (comp_overR X fj ρj hρj ej hej).trans oEL.symm⟩), oEL]
  refine ⟨c, hc, ?_⟩

  have uk : IsUnit (algebraMap R (Localization.Away fS) fk) := by
    rw [← hι, RingHom.comp_apply]; exact IsLocalization.Away.algebraMap_isUnit fS
  have hιρ : ∀ (a : R) (ρ : Localization.Away a →+* S), ρ.comp (algebraMap R _) = algebraMap R S →
      (ι.comp ρ).comp (algebraMap R _) = algebraMap R (Localization.Away fS) := by
    intro a ρ h; rw [RingHom.comp_assoc, h, hι]
  let εk := IsLocalization.Away.lift (S := Localization.Away fk) fk uk
  have hεk : εk.comp (algebraMap R _) = algebraMap R (Localization.Away fS) :=
    IsLocalization.Away.lift_comp _ _
  have hq' := Ideal.Quotient.mk_surjective (I := redI π (Localization.Away fS))
  have hq2' := ker_mk_sq π hsq (Localization.Away fS)
  have rEK := isRed_of_away π hπ g₀ fk ek rek _ εk hεk

  have side : ∀ (fa : R) (Va : X.left.Opens), IsAffineOpen Va → ∀ (ea ta : Sp (Localization.Away fa) ⟶ X.left)
      (ρa : Localization.Away fa →+* S), ρa.comp (algebraMap R _) = algebraMap R S →
      spMap (Localization.awayMap π fa) ≫ ea =
        spMap (algebraMap R₀ (Localization.Away (π fa))) ≫ g₀ →
      (spMap ρa ≫ ea) ⁻¹ᵁ W = ⊤ →
      IsCombIn Va (spMap (awayToAwayRight (P := Localization.Away (fa * fk)) fa fk) ≫ ea)
        (spMap (awayToAwayRight (P := Localization.Away (fa * fk)) fa fk) ≫ ta)
        ![spMap (awayToAwayLeft (P := Localization.Away (fa * fk)) fk fa) ≫ ek]
        ![algebraMap R (Localization.Away (fa * fk)) fk ^ N] →
      IsCombIn W (spMap ι ≫ spMap ρa ≫ ea) (spMap ι ≫ spMap ρa ≫ ta) ![spMap εk ≫ ek] ![ι fS ^ N] := by
    intro fa Va hVa ea ta ρa hρa rea hEa hca
    have ua : IsUnit (algebraMap R (Localization.Away fS) (fa * fk)) := by
      rw [map_mul]; exact (isUnit_of_away fa _ (hιρ fa ρa hρa)).mul uk
    let β := IsLocalization.Away.lift (S := Localization.Away (fa * fk)) (fa * fk) ua
    have hβ : β.comp (algebraMap R _) = algebraMap R (Localization.Away fS) :=
      IsLocalization.Away.lift_comp _ _
    have e1 : β.comp (awayToAwayRight (P := Localization.Away (fa * fk)) fa fk) = ι.comp ρa :=
      away_ext fa _ _ (by rw [RingHom.comp_assoc, awR_comp, hβ, hιρ fa ρa hρa])
    have e2 : β.comp (awayToAwayLeft (P := Localization.Away (fa * fk)) fk fa) = εk :=
      away_ext fk _ _ (by rw [RingHom.comp_assoc, awL_comp, hβ, hεk])
    have h1 := GlobalTheory.T.isAffineCombinationInChart_specMap_comp X.left Va _ _ β (Fin 1) _ _ _ _ hca
    have h1' : IsCombIn Va (spMap ι ≫ spMap ρa ≫ ea) (spMap ι ≫ spMap ρa ≫ ta)
        ![spMap εk ≫ ek] ![ι fS ^ N] := by
      refine isCombIn_congr ?_ ?_ ?_ ?_ h1
      · rw [← Category.assoc, ← spMap_comp, e1, spMap_comp, Category.assoc]
      · rw [← Category.assoc, ← spMap_comp, e1, spMap_comp, Category.assoc]
      · funext i; fin_cases i
        simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_fin_one]
        rw [← Category.assoc, ← spMap_comp, e2]
      · funext i; fin_cases i
        simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_fin_one, map_pow]
        rw [← RingHom.comp_apply, hβ, ← hι, RingHom.comp_apply]
    exact GlobalTheory.T.isAffineCombination_independent_of_chart X.left Va W hVa hW _ _ _ hq' hq2' (Fin 1) _ _ _ _
      (Fin.forall_fin_one.2 (rEK.eq (isRed_comp π hπ g₀ ι hι (isRed_of_away π hπ g₀ fa ea rea S ρa hρa))))
      h1' (GlobalTheory.SecGlue.preimage_spMap_comp_eq_top ι hEa)
  have sj := side fj Vj hVj ej tj ρj hρj rej hA hcj
  have sl := side fl Vl hVl el tl ρl hρl rel (land _ rEL) hcl
  have sc := GlobalTheory.T.isAffineCombinationInChart_specMap_comp X.left W S _ ι (Fin 2) _ _ _ _ hc
  have sc' : IsCombIn W (spMap ι ≫ spMap ρl ≫ el) (spMap ι ≫ c)
      ![spMap ι ≫ spMap ρl ≫ tl, spMap ι ≫ spMap ρj ≫ ej] ![1, 1 - ι fS ^ N] := by
    refine isCombIn_congr rfl rfl ?_ ?_ sc
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp
  obtain ⟨_, _, _, kj⟩ := isCombIn_one sj
  obtain ⟨_, _, _, kl⟩ := isCombIn_one sl
  obtain ⟨_, _, _, _, kc⟩ := isCombIn_two sc'
  have hTJ := land _ rTJ
  have hTL := land _ rTL
  have hEL := land _ rEL
  have hcW : c ⁻¹ᵁ W = ⊤ := hc.2.1
  obtain ⟨M₀, hM⟩ := chartHom_pow_mul_eq X hsm W hW (spMap ρj ≫ tj) c
    ((comp_overR X fj ρj hρj tj htj).trans hcX.symm) hTJ hcW fS (fun x => by
      have k1 := kj x
      have k2 := kl x
      have k3 := kc x
      simp only [GlobalTheory.SecGlue.chartHom_spMap_comp W ι _ hA, GlobalTheory.SecGlue.chartHom_spMap_comp W ι _ hTJ,
        GlobalTheory.SecGlue.chartHom_spMap_comp W ι _ hEL, GlobalTheory.SecGlue.chartHom_spMap_comp W ι _ hTL,
        GlobalTheory.SecGlue.chartHom_spMap_comp W ι _ hcW] at k1 k2 k3
      linear_combination k1 - k3 - k2)
  exact ⟨M₀, fun h₁ h₂ x => hM x⟩
end GlobalTheory.SecGlue.Red
