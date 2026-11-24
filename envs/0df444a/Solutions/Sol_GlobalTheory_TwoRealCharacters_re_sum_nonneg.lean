-- Prove2me | solution 1 for GlobalTheory.TwoRealCharacters.re_sum_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:42:25.220558+00:00
-- url     : https://prove2.me/submissions/1d6121a2-f151-4c8c-8d70-1188751485ce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NegSumLogDerivNonneg

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
theorem _root_.solution (q : ℕ) (χ ψ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1) (hψ : ψ ^ 2 = 1)
    (a : ZMod q) :
    0 ≤ ((1 : DirichletCharacter ℂ q) a).re + (χ a).re + (ψ a).re + ((χ * ψ) a).re := by
  by_cases ha : IsUnit a
  · have hsq : ∀ φ : DirichletCharacter ℂ q, φ ^ 2 = 1 → φ a = 1 ∨ φ a = -1 := by
      intro φ hφ
      apply mul_self_eq_one_iff.mp
      have hval := congrArg (fun ξ : DirichletCharacter ℂ q => ξ a) hφ
      simp only [MulChar.pow_apply' φ two_ne_zero, MulChar.one_apply ha] at hval
      rw [← pow_two]
      exact hval
    rw [MulChar.one_apply ha, MulChar.coeToFun_mul, Pi.mul_apply]
    rcases hsq χ hχ with h1 | h1 <;> rcases hsq ψ hψ with h2 | h2 <;> norm_num [h1, h2]
  · rw [MulChar.map_nonunit _ ha, MulChar.map_nonunit _ ha, MulChar.map_nonunit _ ha,
      MulChar.map_nonunit _ ha]
    simp
end GlobalTheory.TwoRealCharacters
