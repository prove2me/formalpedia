-- Prove2me | solution 1 for GlobalTheory.CharFamily.norm_iteratedFDeriv_char_sub_one_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:10:50.936072+00:00
-- url     : https://prove2.me/submissions/8b6d793f-2944-4ac3-9eb8-e9b753bb2243

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivRemCompLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzFamilyPhaseBound
import Theorems.Thm_GlobalTheory_CharFormDeriv_deriv_affine_cexp
import Theorems.Thm_GlobalTheory_CharFormDeriv_iteratedDeriv_const_mul_cexp
import Theorems.Thm_GlobalTheory_CharFormDeriv_norm_cexp_mul_I_sub_one_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory
open GlobalTheory GlobalTheory.CharFamily
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace GlobalTheory.CharFamily
theorem _root_.solution (L : E →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) (i : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ i (fun x : E => Complex.exp (I * (L x : ℂ)) - 1) x‖
      ≤ 2 * ‖L‖ * (1 + ‖x‖) ^ 1 := by
  have hL0 : 0 ≤ ‖L‖ := norm_nonneg L
  have hx0 : 0 ≤ ‖x‖ := norm_nonneg x
  have ho : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => (y : ℂ)) := Complex.ofRealCLM.contDiff
  have hc : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : ℝ => (1 : ℂ) * Complex.exp (I * y) + 0 * y + (-1)) := by fun_prop
  have e : (fun x : E => Complex.exp (I * (L x : ℂ)) - 1)
      = (fun y : ℝ => (1 : ℂ) * Complex.exp (I * y) + 0 * y + (-1)) ∘ ⇑L := by
    funext x; simp; ring
  rw [e, L.iteratedFDeriv_comp_right hc x (i := i) (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  cases i with
  | zero =>
    rw [iteratedDeriv_zero, pow_zero, mul_one]
    have h0 : (1 : ℂ) * Complex.exp (I * ((L x : ℝ) : ℂ)) + 0 * ((L x : ℝ) : ℂ) + (-1)
        = Complex.exp (((L x : ℝ) : ℂ) * I) - 1 := by ring_nf
    simp only [h0]
    calc _ ≤ 2 * |L x| := GlobalTheory.CharFormDeriv.norm_cexp_mul_I_sub_one_le (L x)
      _ ≤ 2 * (‖L‖ * ‖x‖) := by gcongr; rw [← Real.norm_eq_abs]; exact L.le_opNorm x
      _ ≤ 2 * ‖L‖ * (1 + ‖x‖) ^ 1 := by nlinarith
  | succ j =>
    rw [iteratedDeriv_succ', GlobalTheory.CharFormDeriv.deriv_affine_cexp]
    have hd : (fun y : ℝ => (1 : ℂ) * I * Complex.exp (I * y) + 0)
        = fun y : ℝ => I * Complex.exp (I * y) := by funext y; ring
    rw [hd, GlobalTheory.CharFormDeriv.iteratedDeriv_const_mul_cexp]
    have hexp : I * ((L x : ℝ) : ℂ) = ((L x : ℝ) : ℂ) * I := by ring
    rw [norm_mul, norm_mul, hexp, Complex.norm_exp_ofReal_mul_I, norm_pow, Complex.norm_I]
    simp only [one_pow, mul_one, one_mul]
    calc ‖L‖ ^ (j + 1) ≤ ‖L‖ ^ 1 := pow_le_pow_of_le_one hL0 hL (by omega)
      _ ≤ 2 * ‖L‖ * (1 + ‖x‖) ^ 1 := by nlinarith
end GlobalTheory.CharFamily
