-- Prove2me | solution 1 for GlobalTheory.TwoRealCharacters.neg_sum_logDeriv_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:55:59.137136+00:00
-- url     : https://prove2.me/submissions/117b5951-7b16-4d43-95a2-2c38a2e7ffb9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NegSumLogDerivNonneg
import Theorems.Thm_GlobalTheory_TwoRealCharacters_hasSum_re_neg_logDeriv
import Theorems.Thm_GlobalTheory_TwoRealCharacters_re_sum_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.TwoRealCharacters
namespace GlobalTheory.TwoRealCharacters
theorem _root_.solution : ∀ (q : ℕ) [NeZero q] (χ ψ : DirichletCharacter ℂ q) (σ : ℝ), χ ^ 2 = 1 → ψ ^ 2 = 1 → 1 < σ → 0 ≤ -((deriv (LFunction (1 : DirichletCharacter ℂ q)) σ / LFunction (1 : DirichletCharacter ℂ q) σ).re + (deriv (LFunction χ) σ / LFunction χ σ).re + (deriv (LFunction ψ) σ / LFunction ψ σ).re + (deriv (LFunction (χ * ψ)) σ / LFunction (χ * ψ) σ).re) := by
  intro q _ χ ψ σ hχ hψ hσ
  have h := (((hasSum_re_neg_logDeriv q 1 σ hσ).add (hasSum_re_neg_logDeriv q χ σ hσ)).add
    (hasSum_re_neg_logDeriv q ψ σ hσ)).add (hasSum_re_neg_logDeriv q (χ * ψ) σ hσ)
  have hnn := h.nonneg fun n => by
    have h1 := re_sum_nonneg q χ ψ hχ hψ (n : ZMod q)
    have h2 : 0 ≤ vonMangoldt n / (n : ℝ) ^ σ :=
      div_nonneg vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) σ)
    have h3 := mul_nonneg h1 h2
    linarith
  linarith
end GlobalTheory.TwoRealCharacters
