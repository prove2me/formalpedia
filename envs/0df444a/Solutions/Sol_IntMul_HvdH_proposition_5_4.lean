-- Prove2me | solution 1 for IntMul.HvdH.proposition_5_4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-09T14:38:17.081994+00:00
-- url     : https://prove2.me/submissions/711c2104-6b27-4576-93d6-47ae76acbd4d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_IntMul_HvdH_clocked_recursive_multiplier
import Theorems.Thm_IntMul_HvdH_proposition_5_4_of_clocked_step

open IntMul

theorem solution (d : ℕ) (hd : 2 ≤ d) :
    ∃ M : MultitapeTM, (∀ n : ℕ, 1 ≤ n → ∃ τ : ℝ, MultipliesAt M n τ) ∧
      ∃ C : ℝ, ∀ n : ℕ, 2 ^ (d ^ 12) ≤ n →
        ∀ b p T r : ℕ, b = Nat.clog 2 n → p = 6 * b →
          (∃ k : ℕ, T = 2 ^ k) → 4 * (n : ℝ) / b ≤ T → (T : ℝ) < 8 * (n : ℝ) / b →
          (∃ j : ℕ, r = 2 ^ j) → (T : ℝ) ^ ((1 : ℝ) / d) ≤ r →
          (r : ℝ) < 2 * (T : ℝ) ^ ((1 : ℝ) / d) →
          sInf {τ : ℝ | MultipliesAt M n τ} <
            12 * (T : ℝ) / r * sInf {τ : ℝ | MultipliesAt M (3 * r * p) τ} +
              C * ((n : ℝ) * Real.log n) := by
  obtain ⟨M, hcorrect, C, hclock⟩ := IntMul.HvdH.clocked_recursive_multiplier d hd
  exact IntMul.HvdH.proposition_5_4_of_clocked_step d hd M hcorrect C hclock
