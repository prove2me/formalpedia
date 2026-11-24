-- Prove2me | solution 1 for GlobalTheory.GLFirstColumn.lintegral_blk_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:31:17.293881+00:00
-- url     : https://prove2.me/submissions/1890c709-cc07-4b9b-95fd-8db35ed9421f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MeasurePreservingCons
import Theorems.Thm_GlobalTheory_GLFirstColumn_of_invM
import Theorems.Thm_GlobalTheory_GLFirstColumn_continuous_detM
import Theorems.Thm_GlobalTheory_GLFirstColumn_wt_eq_zero
import Theorems.Thm_GlobalTheory_GLFirstColumn_lintegral_inv
import Theorems.Thm_GlobalTheory_GLFirstColumn_det_blk
import Theorems.Thm_GlobalTheory_GLFirstColumn_inv_blk
import Theorems.Thm_GlobalTheory_GLFirstColumn_measurable_blk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped ENNReal
open GlobalTheory GlobalTheory.GLFirstColumn
namespace GlobalTheory.GLFirstColumn
theorem _root_.solution {k : ℕ} (ψ : (Fin (k + 1) → Fin (k + 1) → ℂ) → ℝ≥0∞)
    (hψ : Measurable ψ) :
    ∫⁻ m : Fin k → Fin k → ℂ, ∫⁻ r : Fin k → ℂ, ψ (invM (blk r m)) * wt (blk r m) =
      ∫⁻ h : Fin k → Fin k → ℂ, ∫⁻ T : Fin k → ℂ, ψ (blk (T ᵥ* Matrix.of h) h) *
        ENNReal.ofReal (‖(Matrix.of h).det‖ ^ 2 * (‖(Matrix.of h).det‖ ^ 2)⁻¹ ^ k) := by
  have hv : Measurable fun p : (Fin k → Fin k → ℂ) × (Fin k → ℂ) => p.2 ᵥ* Matrix.of p.1 := by
    refine Continuous.measurable (continuous_pi fun b => ?_)
    simp only [vecMul, dotProduct, of_apply]
    fun_prop
  have hb : Measurable fun p : (Fin k → Fin k → ℂ) × (Fin k → ℂ) =>
      ψ (blk (p.2 ᵥ* Matrix.of p.1) p.1) := hψ.comp (measurable_blk hv measurable_fst)
  let G : (Fin k → Fin k → ℂ) → ℝ≥0∞ := fun h =>
    (∫⁻ T : Fin k → ℂ, ψ (blk (T ᵥ* Matrix.of h) h)) * ENNReal.ofReal (‖(Matrix.of h).det‖ ^ 2)
  have hG : Measurable G := hb.lintegral_prod_right'.mul
    (continuous_detM.norm.measurable.pow_const 2).ennreal_ofReal
  calc _ = ∫⁻ m, G (invM m) * wt m := by
        refine lintegral_congr fun m => ?_
        by_cases hm : (Matrix.of m).det = 0
        · simp only [wt_eq_zero m hm, wt_eq_zero _ ((det_blk _ m).trans hm), mul_zero,
            lintegral_zero]
        · have hw : ∀ r : Fin k → ℂ, wt (blk r m) =
              ENNReal.ofReal (‖(Matrix.of (invM m)).det‖ ^ 2) * wt m := fun r => by
            unfold wt
            rw [det_blk, of_invM, det_nonsing_inv, Ring.inverse_eq_inv', norm_inv, inv_pow _ 2,
              ← ENNReal.ofReal_mul (by positivity), pow_succ']
          simp only [hw, G]
          rw [lintegral_mul_const' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
            (show wt m ≠ ⊤ from ENNReal.ofReal_ne_top)), mul_assoc, ← lintegral_neg_eq_self]
          congr 1
          refine lintegral_congr fun T => ?_
          exact congrArg ψ (inv_blk T m hm)
    _ = ∫⁻ h, G h * wt h := lintegral_inv G hG
    _ = _ := by
        refine lintegral_congr fun h => ?_
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, ENNReal.ofReal_mul (by positivity),
          ← mul_assoc]
        rfl
end GlobalTheory.GLFirstColumn
