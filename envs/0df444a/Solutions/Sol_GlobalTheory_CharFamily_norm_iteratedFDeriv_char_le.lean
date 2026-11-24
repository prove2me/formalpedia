-- Prove2me | solution 1 for GlobalTheory.CharFamily.norm_iteratedFDeriv_char_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:10:49.566678+00:00
-- url     : https://prove2.me/submissions/dc43ec1e-db9e-4480-9688-0365bdea0507

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivRemCompLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzFamilyPhaseBound
import Theorems.Thm_GlobalTheory_CharFormDeriv_iteratedDeriv_const_mul_cexp


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
theorem _root_.solution (L : E →L[ℝ] ℝ) (i : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ i (fun x : E => Complex.exp (I * (L x : ℂ))) x‖ ≤ ‖L‖ ^ i := by
  have ho : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => (y : ℂ)) := Complex.ofRealCLM.contDiff
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => (1 : ℂ) * Complex.exp (I * (y : ℂ))) := by
    fun_prop
  have e : (fun x : E => Complex.exp (I * (L x : ℂ)))
      = (fun y : ℝ => (1 : ℂ) * Complex.exp (I * (y : ℂ))) ∘ ⇑L := by
    funext x; simp
  rw [e, L.iteratedFDeriv_comp_right hc x (i := i) (by exact_mod_cast le_top)]
  calc _ ≤ ‖iteratedFDeriv ℝ i (fun y : ℝ => (1 : ℂ) * Complex.exp (I * (y : ℂ))) (L x)‖
          * ∏ _j : Fin i, ‖L‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖L‖ ^ i := by
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, GlobalTheory.CharFormDeriv.iteratedDeriv_const_mul_cexp]
        have hexp : I * ((L x : ℝ) : ℂ) = ((L x : ℝ) : ℂ) * I := by ring
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        rw [norm_mul, hexp, Complex.norm_exp_ofReal_mul_I, norm_mul, norm_pow, Complex.norm_I]
        simp
end GlobalTheory.CharFamily
