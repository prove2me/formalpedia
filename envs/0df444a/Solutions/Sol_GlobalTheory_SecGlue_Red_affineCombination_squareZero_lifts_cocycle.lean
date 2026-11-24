-- Prove2me | solution 1 for GlobalTheory.SecGlue.Red.affineCombination_squareZero_lifts_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:54:43.859623+00:00
-- url     : https://prove2.me/submissions/f07e4a51-7ffd-4a9a-9ec4-21851a07abc8

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
import Theorems.Thm_GlobalTheory_SecGlue_Red_isCombIn_congr
import Theorems.Thm_GlobalTheory_SecGlue_Red_isCombIn_one
import Theorems.Thm_GlobalTheory_SecGlue_Red_isCombIn_two
import Theorems.Thm_GlobalTheory_SecGlue_Red_IsRed_eq
import Theorems.Thm_GlobalTheory_SecGlue_Red_isRed_of_away
import Theorems.Thm_GlobalTheory_SecGlue_Red_ker_mk_sq
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
namespace GlobalTheory.SecGlue.Red
theorem _root_.solution {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀)
    (hπ : Function.Surjective π) (hsq : RingHom.ker π ^ 2 = ⊥) (X : Over (Sp R))
    (g₀ : Sp R₀ ⟶ X.left) (fj fl fk : R) (Vj Vl W : X.left.Opens) (hVj : IsAffineOpen Vj)
    (hVl : IsAffineOpen Vl) (hW : IsAffineOpen W)
    (ej tj t'j : Sp (Localization.Away fj) ⟶ X.left) (el tl t'l : Sp (Localization.Away fl) ⟶ X.left)
    (rej : spMap (Localization.awayMap π fj) ≫ ej = spMap (algebraMap R₀ (Localization.Away (π fj))) ≫ g₀)
    (rtj : spMap (Localization.awayMap π fj) ≫ tj = spMap (algebraMap R₀ (Localization.Away (π fj))) ≫ g₀)
    (rel : spMap (Localization.awayMap π fl) ≫ el = spMap (algebraMap R₀ (Localization.Away (π fl))) ≫ g₀)
    (rtl : spMap (Localization.awayMap π fl) ≫ tl = spMap (algebraMap R₀ (Localization.Away (π fl))) ≫ g₀)
    (N M M₀ : ℕ) (hM : M₀ ≤ M)
    (h'j : IsCombIn Vj ej t'j ![tj] ![algebraMap R (Localization.Away fj) fk ^ M])
    (h'l : IsCombIn Vl el t'l ![tl] ![algebraMap R (Localization.Away fl) fk ^ M])
    (S : Type) [CommRing S] [Algebra R S] (ρj : Localization.Away fj →+* S)
    (ρl : Localization.Away fl →+* S) (hρj : ρj.comp (algebraMap R _) = algebraMap R S)
    (hρl : ρl.comp (algebraMap R _) = algebraMap R S) (hA : (spMap ρj ≫ ej) ⁻¹ᵁ W = ⊤)
    (c : Sp S ⟶ X.left)
    (hc : IsCombIn W (spMap ρl ≫ el) c ![spMap ρl ≫ tl, spMap ρj ≫ ej] ![1, 1 - algebraMap R S fk ^ N])
    (hM₀ : ∀ (h₁ : (spMap ρj ≫ tj) ⁻¹ᵁ W = ⊤) (h₂ : c ⁻¹ᵁ W = ⊤) x,
      algebraMap R S fk ^ M₀ * chartHom W (spMap ρj ≫ tj) h₁ x =
        algebraMap R S fk ^ M₀ * chartHom W c h₂ x) :
    IsCombIn W (spMap ρl ≫ el) (spMap ρj ≫ t'j) ![spMap ρl ≫ t'l, spMap ρj ≫ ej]
      ![1, 1 - algebraMap R S fk ^ (N + M)] := by
  set fS := algebraMap R S fk with hfS
  have rA := isRed_of_away π hπ g₀ fj ej rej S ρj hρj
  have rTJ := isRed_of_away π hπ g₀ fj tj rtj S ρj hρj
  have rEL := isRed_of_away π hπ g₀ fl el rel S ρl hρl
  have rTL := isRed_of_away π hπ g₀ fl tl rtl S ρl hρl
  have hq := Ideal.Quotient.mk_surjective (I := redI π S)
  have hq2 := ker_mk_sq π hsq S
  have land : ∀ u, IsRed π hπ g₀ S u → u ⁻¹ᵁ W = ⊤ := fun u hu =>
    (GlobalTheory.T.preimage_eq_of_square_zero_thickening S _ _ hq hq2 X.left u _ (hu.eq rA) W).trans hA
  have move : ∀ (fa : R) (Va : X.left.Opens), IsAffineOpen Va →
      ∀ (ea ta t'a : Sp (Localization.Away fa) ⟶ X.left) (ρa : Localization.Away fa →+* S),
      ρa.comp (algebraMap R _) = algebraMap R S →
      IsRed π hπ g₀ S (spMap ρa ≫ ea) → IsRed π hπ g₀ S (spMap ρa ≫ ta) →
      IsCombIn Va ea t'a ![ta] ![algebraMap R (Localization.Away fa) fk ^ M] →
      IsCombIn W (spMap ρa ≫ ea) (spMap ρa ≫ t'a) ![spMap ρa ≫ ta] ![fS ^ M] := by
    intro fa Va hVa ea ta t'a ρa hρa rE rT h
    have a1 := GlobalTheory.T.isAffineCombinationInChart_specMap_comp X.left Va _ S ρa (Fin 1) _ _ _ _ h
    have a1' : IsCombIn Va (spMap ρa ≫ ea) (spMap ρa ≫ t'a) ![spMap ρa ≫ ta] ![fS ^ M] := by
      refine isCombIn_congr rfl rfl ?_ ?_ a1
      · funext i; fin_cases i; rfl
      · funext i; fin_cases i
        simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_fin_one, map_pow]
        rw [← RingHom.comp_apply, hρa]
    exact GlobalTheory.T.isAffineCombination_independent_of_chart X.left Va W hVa hW S _ _ hq hq2 (Fin 1) _ _ _ _
      (Fin.forall_fin_one.2 (rT.eq rE)) a1' (land _ rE)
  obtain ⟨hA', hT'J, hTJ, k1⟩ := isCombIn_one (move fj Vj hVj ej tj t'j ρj hρj rA rTJ h'j)
  obtain ⟨hEL, hT'L, hTL, k2⟩ := isCombIn_one (move fl Vl hVl el tl t'l ρl hρl rEL rTL h'l)
  obtain ⟨_, hcW, _, _, k3⟩ := isCombIn_two hc
  refine ⟨hEL, hT'J, Fin.forall_fin_two.2 ⟨hT'L, hA⟩, fun x => ?_⟩
  have k4 := hM₀ hTJ hcW x
  have k1 := k1 x
  have k2 := k2 x
  have k3 := k3 x
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hM
  rw [Fin.sum_univ_two]
  show chartHom W _ hT'J x = chartHom W _ hEL x +
    ((1 : S) * (chartHom W (spMap ρl ≫ t'l) hT'L x - chartHom W _ hEL x) +
      (1 - fS ^ (N + (M₀ + d))) * (chartHom W (spMap ρj ≫ ej) hA x - chartHom W _ hEL x))
  linear_combination k1 - k2 + fS ^ (M₀ + d) * k3 + fS ^ d * k4
end GlobalTheory.SecGlue.Red
