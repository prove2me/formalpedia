-- Prove2me | solution 1 for GlobalTheory.isIntegral_modularJ_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:52:14.277971+00:00
-- url     : https://prove2.me/submissions/b40252cc-f7ef-413c-a942-1a788ca3ce11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsPolynomialModularJOfHasQExpansion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ModularJExpansionAndPolynomialAndIsIntegral
import Theorems.Thm_GlobalTheory_HasUnitLeadingExpansion_one
import Theorems.Thm_GlobalTheory_HasUnitLeadingExpansion_mul
import Theorems.Thm_GlobalTheory_HasUnitLeadingExpansion_isIntegral_modularJ
import Theorems.Thm_GlobalTheory_hasUnitLeadingExpansion_sub
import Theorems.Thm_GlobalTheory_coe_fixedDetToGL_smul
import Theorems.Thm_GlobalTheory_fixedDetToGL_smul_smul
import Theorems.Thm_GlobalTheory_exists_fixedDetToGL_smul_eq
import Theorems.Thm_GlobalTheory_HasQExpansion_mul
import Theorems.Thm_GlobalTheory_modularJ_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperHalfPlane ModularForm Complex Function Filter PowerSeries
open scoped Topology MatrixGroups Manifold Real
noncomputable section
open GlobalTheory
local notation "𝕢" => Function.Periodic.qParam
namespace GlobalTheory
theorem _root_.solution {n : ℕ} (hsq : ¬ IsSquare n)
    (M : FixedDetMatrix (Fin 2) ℤ n) {τ₀ : ℍ}
    (hM : M.1 0 0 * (τ₀ : ℂ) + M.1 0 1 = (M.1 1 0 * τ₀ + M.1 1 1) * τ₀) :
    IsIntegral ℤ (modularJ τ₀) := by
  classical
  have hn : n ≠ 0 := by rintro rfl; exact hsq IsSquare.zero
  let F : FixedDetMatrix (Fin 2) ℤ n → ℍ → ℂ := fun A τ ↦ modularJ (fixedDetToGL hn A • τ)
  have hrep (A : FixedDetMatrix (Fin 2) ℤ n) : ∃ B ∈ FixedDetMatrices.reps n, F B = F A := by
    have hs (γ : SL(2, ℤ)) (B : FixedDetMatrix (Fin 2) ℤ n) : F (γ • B) = F B := by
      ext τ
      simp only [F, fixedDetToGL_smul_smul, modularJ_smul]
    induction A using FixedDetMatrices.induction_on (m := n) (by exact_mod_cast hn) with
    | h0 A h1 h2 h3 h4 => exact ⟨A, ⟨h1, h2, h3, h4⟩, rfl⟩
    | hS B hB => rwa [hs]
    | hT B hB => rwa [hs]
  have hfin : (Set.range F).Finite :=
    ((Set.toFinite (FixedDetMatrices.reps (n : ℤ))).image F).subset <| by
      rintro _ ⟨A, rfl⟩
      exact hrep A
  let Φ : ℍ → ℂ := ∏ G ∈ hfin.toFinset, fun τ ↦ modularJ τ - G τ
  have hΦ : HasUnitLeadingExpansion n Φ := by
    refine Finset.prod_induction _ _ (fun _ _ ↦ .mul) (.one _) fun G hG ↦ ?_
    obtain ⟨A, rfl⟩ := hfin.mem_toFinset.mp hG
    obtain ⟨B, ⟨h1, h2, -, -⟩, hB⟩ := hrep A
    rw [← hB]
    have hdet : B.1 0 0 * B.1 1 1 = n := by simpa [Matrix.det_fin_two, h1] using B.2
    have h3 : 0 < B.1 1 1 := by
      have : 0 < B.1 0 0 * B.1 1 1 := by rw [hdet]; positivity
      exact (pos_iff_pos_of_mul_pos this).mp h2
    obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le h2.le
    obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le h3.le
    refine hasUnitLeadingExpansion_sub (a := a) (d := d) (b := B.1 0 1) ?_ hn hsq fun τ ↦ ?_
    · rw [ha, hd] at hdet
      exact_mod_cast hdet
    · simp [coe_fixedDetToGL_smul, h1, ha, hd]
  have hmem (γ : SL(2, ℤ)) (G : ℍ → ℂ) (hG : G ∈ hfin.toFinset) :
      (fun τ ↦ G (γ • τ)) ∈ hfin.toFinset := by
    obtain ⟨A, rfl⟩ := hfin.mem_toFinset.mp hG
    obtain ⟨B, hB⟩ := exists_fixedDetToGL_smul_eq hn γ A
    exact hfin.mem_toFinset.mpr ⟨B, funext fun τ ↦ by simp only [F, hB]⟩
  refine hΦ.isIntegral_modularJ hn (fun γ τ ↦ ?_) ?_
  · simp only [Φ, Finset.prod_apply, modularJ_smul]
    exact Finset.prod_nbij' (fun G τ ↦ G (γ • τ)) (fun G τ ↦ G (γ⁻¹ • τ)) (hmem γ) (hmem γ⁻¹)
      (fun G _ ↦ by simp only [smul_inv_smul]) (fun G _ ↦ by simp only [inv_smul_smul])
      fun _ _ ↦ rfl
  · simp only [Φ, Finset.prod_apply]
    refine Finset.prod_eq_zero (hfin.mem_toFinset.mpr ⟨M, rfl⟩) ?_
    have : fixedDetToGL hn M • τ₀ = τ₀ := by
      ext
      have h := denom_ne_zero (fixedDetToGL hn M) τ₀
      rw [coe_fixedDetToGL_smul, hM, mul_div_cancel_left₀]
      simpa [denom, fixedDetToGL] using h
    simp only [F, this, sub_self]
end GlobalTheory
