-- Prove2me | solution 1 for MultiSecretary.BR.state_space_reduction
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T22:52:59.568864+00:00
-- url     : https://prove2.me/submissions/be25ddc4-7979-43ae-a40c-a88cb4ce1cbe

import Mathlib
import Definitions.Def_MultiSecretary_BR_Model

open MultiSecretary.BR in
theorem solution {m : ℕ} (I : Instance m) (v : ℕ → ℝ → ℕ → ℝ) (g : ℕ → ℕ → ℝ)
    (hv : ∀ ℓ κ w, 1 ≤ ℓ → 1 ≤ κ → 0 ≤ w →
      v ℓ w κ = ∑ j, max (v (ℓ - 1) (w + I.a j) (κ - 1)) (v (ℓ - 1) w κ) * I.f j)
    (hv0 : ∀ κ w, 0 ≤ w → v 0 w κ = w)
    (hvκ : ∀ ℓ w, 1 ≤ ℓ → 0 ≤ w → v ℓ w 0 = w)
    (hg_nonneg : ∀ ℓ κ, 0 ≤ g ℓ κ)
    (hg : ∀ ℓ κ, 1 ≤ ℓ → 1 ≤ κ →
      g ℓ κ = ∑ j, max (I.a j + g (ℓ - 1) (κ - 1)) (g (ℓ - 1) κ) * I.f j)
    (hg0 : ∀ κ, g 0 κ = 0)
    (hgκ : ∀ ℓ, 1 ≤ ℓ → g ℓ 0 = 0) :
    ∀ ℓ κ w, 0 ≤ w → v ℓ w κ = w + g ℓ κ := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro κ w hw
    rw [hv0 κ w hw, hg0 κ, add_zero]
  | succ n ih =>
    intro κ w hw
    rcases Nat.eq_zero_or_pos κ with hκ | hκ
    · subst hκ
      rw [hvκ (n + 1) w (by omega) hw, hgκ (n + 1) (by omega), add_zero]
    · rw [hv (n + 1) κ w (by omega) hκ hw, hg (n + 1) κ (by omega) hκ]
      simp only [Nat.add_sub_cancel]
      have key : ∀ j, max (v n (w + I.a j) (κ - 1)) (v n w κ) * I.f j
          = w * I.f j + max (I.a j + g n (κ - 1)) (g n κ) * I.f j := by
        intro j
        rw [ih (κ - 1) (w + I.a j) (add_nonneg hw (I.a_pos j).le), ih κ w hw,
          add_assoc, max_add_add_left, add_mul]
      rw [Finset.sum_congr rfl (fun j _ => key j), Finset.sum_add_distrib,
        ← Finset.mul_sum, I.f_sum, mul_one]
