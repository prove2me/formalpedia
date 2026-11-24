-- Prove2me | solution 1 for GlobalTheory.LLeft.abel_three
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:42:39.530909+00:00
-- url     : https://prove2.me/submissions/a7ddc2c4-74d6-44cf-bb95-c58b1b9416b8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SummableNinePowMulInvSqSucc
import Theorems.Thm_GlobalTheory_LLeft_abel_step
import Theorems.Thm_GlobalTheory_LLeft_summable_diffPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory
open GlobalTheory.LLeft
namespace GlobalTheory.LLeft
theorem _root_.solution (q : ℕ) (hq : 0 < q) (a : ℕ → ℂ) (hp : Function.Periodic a q)
    (h0 : ∑ n ∈ Finset.range q, a n = 0) (hM : ∀ n, ‖a n‖ ≤ 1) :
    ∃ (b : ℕ → ℂ) (μ₁ μ₂ μ₃ : ℂ), (∀ n, ‖b n‖ ≤ 8 * (q : ℝ) ^ 3) ∧ ‖μ₁‖ ≤ q ∧
      ‖μ₂‖ ≤ 2 * (q : ℝ) ^ 2 ∧ ‖μ₃‖ ≤ 4 * (q : ℝ) ^ 3 ∧
      ∀ s : ℂ, 1 < s.re → ∑' n : ℕ, a n * diffPow 0 s ((n : ℝ) + 1) =
        μ₁ * diffPow 0 s 1 + μ₂ * diffPow 1 s 1 + μ₃ * diffPow 2 s 1 +
          ∑' n : ℕ, b n * diffPow 3 s ((n : ℝ) + 1) := by
  obtain ⟨b₁, μ₁, p₁, z₁, n₁, m₁, e₁⟩ := abel_step q hq a 1 hp h0 hM
  obtain ⟨b₂, μ₂, p₂, z₂, n₂, m₂, e₂⟩ := abel_step q hq b₁ _ p₁ z₁ n₁
  obtain ⟨b₃, μ₃, -, -, n₃, m₃, e₃⟩ := abel_step q hq b₂ _ p₂ z₂ n₂
  refine ⟨b₃, μ₁, μ₂, μ₃, fun n => (n₃ n).trans_eq (by ring), m₁.trans_eq (by ring),
    m₂.trans_eq (by ring), m₃.trans_eq (by ring), fun s hs => ?_⟩
  have hd : ∀ (k n : ℕ), diffPow k s ((n : ℝ) + 1) - diffPow k s (((n + 1 : ℕ) : ℝ) + 1)
      = diffPow (k + 1) s ((n : ℝ) + 1) := by
    intro k n
    simp only [diffPow]; push_cast; rfl
  have hsum : ∀ k : ℕ, Summable (fun n : ℕ => ‖diffPow k s ((n : ℝ) + 1)‖) := fun k =>
    summable_diffPow k s (by have : (0 : ℝ) ≤ k := by positivity
                             linarith)
  have f₁ := e₁ _ (hsum 0)
  have f₂ := e₂ _ (hsum 1)
  have f₃ := e₃ _ (hsum 2)
  simp only [hd] at f₁ f₂ f₃
  simp only [Nat.cast_zero, zero_add] at f₁ f₂ f₃
  rw [f₁, f₂, f₃]
  ring
end GlobalTheory.LLeft
