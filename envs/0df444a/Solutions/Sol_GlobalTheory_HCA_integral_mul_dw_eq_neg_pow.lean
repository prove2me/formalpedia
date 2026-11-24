-- Prove2me | solution 1 for GlobalTheory.HCA.integral_mul_dw_eq_neg_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:03:04.394797+00:00
-- url     : https://prove2.me/submissions/b1ed21ba-41a2-4bbb-9f3a-4f17bf57f33b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DwSmoothLocalLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralMulIterPartialDerivEqNegPow
import Theorems.Thm_GlobalTheory_HCA_dw_perm
import Theorems.Thm_GlobalTheory_HCA_integral_mul_dw_eq_reverse

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction
open GlobalTheory GlobalTheory.HCA
namespace GlobalTheory.HCA
theorem _root_.solution : ∀ (d : ℕ) (U : Set (E d)), IsOpen U → ∀ (w : List (Fin d))
    (u φ : E d → ℂ), ContDiffOn ℝ ∞ u U → ContDiff ℝ ∞ φ → HasCompactSupport φ →
    tsupport φ ⊆ U → ∫ x, u x * dw w φ x = (-1 : ℂ) ^ w.length * ∫ x, dw w u x * φ x := by
  intro d U hU w u φ hu hφ hφc hφs
  rw [integral_mul_dw_eq_reverse hU w u φ hu hφ hφc hφs]
  congr 2
  funext x
  by_cases hx : x ∈ U
  · rw [dw_perm hU (List.reverse_perm w) u hu hx]
  · have : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hφs h))
    simp [this]
end GlobalTheory.HCA
