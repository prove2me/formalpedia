-- Prove2me | solution 1 for GlobalTheory.RealWeil.decay_gau_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:11:37.831186+00:00
-- url     : https://prove2.me/submissions/ef00d134-cfe2-4a42-89d7-91cb5c459f6a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowMulNormGauLe
import Theorems.Thm_GlobalTheory_RealWeil_pow_mul_norm_gau_le
import Theorems.Thm_GlobalTheory_RealWeil_gau_add
import Theorems.Thm_GlobalTheory_RealWeil_contDiff_gau
import Theorems.Thm_GlobalTheory_RealWeil_exists_shift_form

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder FourierTransform
open GlobalTheory GlobalTheory.RealWeil
namespace GlobalTheory.RealWeil
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] {J : V ≃ₗᵢ[ℝ] V} {ρ : V → B →L[ℂ] B}
    (h : IsHeis (omJ J) ρ) {f : B} (hf : Sm ρ f) (k n : ℕ) :
    ∃ C, ∀ v, ‖v‖ ^ k * ‖iteratedFDeriv ℝ n (fun u => gau u • ρ u f) v‖ ≤ C := by
  set F : V → B := fun u => gau u • ρ u f with hF
  have hFs : ContDiff ℝ ∞ F := contDiff_gau.smul hf
  have hE : ContDiff ℝ ∞ (fun z : ℂ => cexp z) := Complex.contDiff_exp
  have hN : ((n : ℕ) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
      (‖iteratedFDeriv ℝ i (fun z : ℂ => cexp z) 0‖ * (2 * π) ^ i) *
      ‖iteratedFDeriv ℝ (n - i) F 0‖ * ((k + i).factorial * Real.exp 1), fun v => ?_⟩
  obtain ⟨l, hl, hlt⟩ := exists_shift_form J v
  have hshift : (fun t => F (t + v)) = fun t => (gau v • ρ v) (cexp (l t) • F t) := by
    funext t
    simp only [hF, _root_.smul_apply, map_smul, smul_smul]
    rw [add_comm t v, h.2.1 v t f, smul_smul]
    congr 1
    have key : cexp (-(π : ℂ) * (⟪v, t⟫ : ℝ)) = cexp (l t) * cexp (π * I * (omJ J v t : ℂ)) := by
      rw [hlt t, ← Complex.exp_add]; congr 1; ring
    rw [gau_add, key]
    ring
  have hG : ContDiff ℝ ∞ (fun t => cexp (l t)) := hE.comp l.contDiff
  have hρ1 : ‖ρ v‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by rw [h.2.2.1, one_mul]
  have hL : ‖(gau v • ρ v).restrictScalars ℝ‖ ≤ ‖gau v‖ := by
    rw [ContinuousLinearMap.norm_restrictScalars]
    calc ‖gau v • ρ v‖ ≤ ‖gau v‖ * ‖ρ v‖ := norm_smul_le _ _
      _ ≤ ‖gau v‖ * 1 := by gcongr
      _ = ‖gau v‖ := mul_one _
  have hexp : ∀ i : ℕ, ‖iteratedFDeriv ℝ i (fun t => cexp (l t)) 0‖ ≤
      ‖iteratedFDeriv ℝ i (fun z : ℂ => cexp z) 0‖ * (2 * π * ‖v‖) ^ i := by
    intro i
    have e1 : (fun t => cexp (l t)) = (fun z : ℂ => cexp z) ∘ (l : V → ℂ) := rfl
    rw [e1, l.iteratedFDeriv_comp_right hE 0 (by exact_mod_cast le_top), map_zero]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    gcongr
  have hD : ‖iteratedFDeriv ℝ n F v‖ ≤ ‖gau v‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
      (‖iteratedFDeriv ℝ i (fun z : ℂ => cexp z) 0‖ * (2 * π * ‖v‖) ^ i) *
      ‖iteratedFDeriv ℝ (n - i) F 0‖ := by
    have e0 : iteratedFDeriv ℝ n F v = iteratedFDeriv ℝ n (fun t => F (t + v)) 0 := by
      rw [iteratedFDeriv_comp_add_right, zero_add]
    have e2 : (fun t => (gau v • ρ v) (cexp (l t) • F t)) =
        ((gau v • ρ v).restrictScalars ℝ) ∘ (fun t => cexp (l t) • F t) := rfl
    rw [e0, hshift, e2]
    refine (ContinuousLinearMap.norm_iteratedFDeriv_comp_left _ (hG.smul hFs).contDiffAt hN).trans ?_
    refine mul_le_mul hL ?_ (norm_nonneg _) (norm_nonneg _)
    refine (norm_iteratedFDeriv_smul_le hG hFs 0 hN).trans (Finset.sum_le_sum fun i _ => ?_)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hexp i) (by positivity))
      (norm_nonneg _)
  calc ‖v‖ ^ k * ‖iteratedFDeriv ℝ n F v‖
      ≤ ‖v‖ ^ k * (‖gau v‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (‖iteratedFDeriv ℝ i (fun z : ℂ => cexp z) 0‖ * (2 * π * ‖v‖) ^ i) *
        ‖iteratedFDeriv ℝ (n - i) F 0‖) := mul_le_mul_of_nonneg_left hD (by positivity)
    _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (‖iteratedFDeriv ℝ i (fun z : ℂ => cexp z) 0‖ * (2 * π) ^ i) *
        ‖iteratedFDeriv ℝ (n - i) F 0‖ * (‖v‖ ^ (k + i) * ‖gau v‖) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_pow, pow_add]
        ring
    _ ≤ _ := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (pow_mul_norm_gau_le _ _) (by positivity)
end GlobalTheory.RealWeil
