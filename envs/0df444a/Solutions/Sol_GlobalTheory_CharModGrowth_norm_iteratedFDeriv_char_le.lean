-- Prove2me | solution 1 for GlobalTheory.CharModGrowth.norm_iteratedFDeriv_char_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:10:42.308719+00:00
-- url     : https://prove2.me/submissions/9a952795-f534-4b8c-862d-b00a660e8d63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivRemCompLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ModulatedSchwartzSeminormPolynomial
import Theorems.Thm_GlobalTheory_CharFormDeriv_iteratedDeriv_const_mul_cexp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open GlobalTheory GlobalTheory.CharModGrowth
namespace GlobalTheory.CharModGrowth
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] ℝ) (t : ℝ) (n : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ n (fun x : V => Complex.exp ((I * t) * (L x : ℂ))) x‖ ≤ (|t| * ‖L‖) ^ n := by
  have ho : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => (y : ℂ)) := Complex.ofRealCLM.contDiff
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => (1 : ℂ) * Complex.exp ((I * t) * (y : ℂ))) := by
    fun_prop
  have e : (fun x : V => Complex.exp ((I * t) * (L x : ℂ)))
      = (fun y : ℝ => (1 : ℂ) * Complex.exp ((I * t) * (y : ℂ))) ∘ ⇑L := by
    funext x; simp
  rw [e, L.iteratedFDeriv_comp_right hc x (i := n) (by exact_mod_cast le_top)]
  calc _ ≤ ‖iteratedFDeriv ℝ n (fun y : ℝ => (1 : ℂ) * Complex.exp ((I * t) * (y : ℂ))) (L x)‖
          * ∏ _j : Fin n, ‖L‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = (|t| * ‖L‖) ^ n := by
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
          GlobalTheory.CharFormDeriv.iteratedDeriv_const_mul_cexp]
        have hexp : (I * t) * ((L x : ℝ) : ℂ) = ((t * L x : ℝ) : ℂ) * I := by push_cast; ring
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        rw [norm_mul, hexp, Complex.norm_exp_ofReal_mul_I, norm_mul, norm_pow, norm_mul,
          Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
        simp [mul_pow]
end GlobalTheory.CharModGrowth
