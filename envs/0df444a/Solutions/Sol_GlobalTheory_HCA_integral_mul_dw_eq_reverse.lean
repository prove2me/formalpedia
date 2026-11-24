-- Prove2me | solution 1 for GlobalTheory.HCA.integral_mul_dw_eq_reverse
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:47:48.92608+00:00
-- url     : https://prove2.me/submissions/c9457610-8319-4286-9aeb-c56336a48685

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DwSmoothLocalLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralMulIterPartialDerivEqNegPow
import Theorems.Thm_GlobalTheory_HCA_integral_mul_partial_eq_neg
import Theorems.Thm_GlobalTheory_HCA_dw_contDiff_tsupport
import Theorems.Thm_GlobalTheory_HCA_dw_append
import Theorems.Thm_GlobalTheory_HCA_contDiffOn_dw_of_isOpen


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
theorem _root_.solution {d : ℕ} {U : Set (E d)} (hU : IsOpen U) (w : List (Fin d)) :
    ∀ (u φ : E d → ℂ), ContDiffOn ℝ ∞ u U → ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ U →
      ∫ x, u x * dw w φ x = (-1 : ℂ) ^ w.length * ∫ x, dw w.reverse u x * φ x := by
  induction w with
  | nil => intro u φ _ _ _ _; simp [dw]
  | cons j w ih =>
    intro u φ hu hφ hφc hφs
    obtain ⟨hψ, hψs⟩ := dw_contDiff_tsupport w hφ
    have hψc : HasCompactSupport (dw w φ) := IsCompact.of_isClosed_subset hφc (isClosed_tsupport _) hψs
    have step := integral_mul_partial_eq_neg hU j hu hψ hψc (hψs.trans hφs)
    have hu1 : ContDiffOn ℝ ∞ (dw [j] u) U := contDiffOn_dw_of_isOpen hU [j] u hu
    have ih' := ih (dw [j] u) φ hu1 hφ hφc hφs
    have e : dw w.reverse (dw [j] u) = dw (j :: w).reverse u := by
      rw [List.reverse_cons, dw_append]
    show ∫ x, u x * fderiv ℝ (dw w φ) x (ev j) = _
    rw [step]
    change -∫ x, dw [j] u x * dw w φ x = _
    rw [ih', e, List.length_cons, pow_succ]
    ring
end GlobalTheory.HCA
