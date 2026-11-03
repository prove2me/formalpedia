-- Prove2me | solution 1 for MultiPriceOnline.Hardness.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T20:05:10.0487+00:00
-- url     : https://prove2.me/submissions/89ab6657-d590-4f94-bce4-da045270773c

import Mathlib
import Definitions.Def_MultiPriceOnline_Hardness_PriceSet

open MultiPriceOnline.Hardness

private lemma r_mono_step {m : ℕ} {r : ℕ → ℝ} (hr : MultiPriceOnline.Balance.IsPriceSet m r) :
    ∀ j, 1 ≤ j → j ≤ m → 0 < r j := by
  intro j hj1 hjm
  induction j with
  | zero => omega
  | succ k ih =>
    rcases eq_or_lt_of_le hj1 with h | h
    · rw [← h]; exact hr.1
    · have hk1 : 1 ≤ k := by omega
      have hkm : k < m := by omega
      have hk_pos : 0 < r k := ih hk1 (by omega)
      have hlt : r k < r (k + 1) := hr.2 k hk1 hkm
      linarith

theorem solution {m : ℕ} {r α : ℕ → ℝ} (hm : 1 ≤ m) (hr : MultiPriceOnline.Balance.IsPriceSet m r)
    (hα : MultiPriceOnline.Balance.IsBookingLimits m r α) :
    (∃ B : ℕ → ℝ, IsPhaseB m r α B ∧ 0 < B m ∧ ∀ j : ℕ, 2 ≤ j → j ≤ m → B j < B (j - 1)) ∧
    ∀ B B' : ℕ → ℝ, IsPhaseB m r α B → IsPhaseB m r α B' →
      ∀ j : ℕ, 1 ≤ j → j ≤ m → B j = B' j := by
  have hr_pos : ∀ j, 1 ≤ j → j ≤ m → 0 < r j := r_mono_step hr
  have hr1_pos : 0 < r 1 := hr.1
  have hexp_pos : ∀ j, 0 < Real.exp (-α j) := fun j => Real.exp_pos (-α j)
  have hB_eq : ∀ (B : ℕ → ℝ), IsPhaseB m r α B → ∀ j, 1 ≤ j → j ≤ m →
      B j * (r j * Real.exp (-α j)) = r 1 * Real.exp (-α 1) := by
    intro B hB j hj1 hjm
    rcases eq_or_lt_of_le hj1 with rfl | hj2
    · rw [hB.1, one_mul]
    · have := hB.2 j hj2 hjm
      linarith
  refine ⟨?_, ?_⟩
  · let B : ℕ → ℝ := fun j => (r 1 * Real.exp (-α 1)) / (r j * Real.exp (-α j))
    have hB : IsPhaseB m r α B := by
      refine ⟨?_, ?_⟩
      · dsimp [B]
        exact div_self (ne_of_gt (mul_pos hr1_pos (hexp_pos 1)))
      · intro j hj2 hjm
        dsimp [B]
        have hpos : 0 < r j * Real.exp (-α j) := mul_pos (hr_pos j (by omega) hjm) (hexp_pos j)
        calc
          r 1 * Real.exp (-α 1) / (r j * Real.exp (-α j)) * r j * Real.exp (-α j)
            = r 1 * Real.exp (-α 1) / (r j * Real.exp (-α j)) * (r j * Real.exp (-α j)) := by ring
          _ = r 1 * Real.exp (-α 1) := div_mul_cancel₀ _ (ne_of_gt hpos)
    have hB_pos : ∀ j, 1 ≤ j → j ≤ m → 0 < B j := by
      intro j hj1 hjm
      dsimp [B]
      exact div_pos (mul_pos hr1_pos (hexp_pos 1)) (mul_pos (hr_pos j hj1 hjm) (hexp_pos j))
    refine ⟨B, hB, hB_pos m hm le_rfl, ?_⟩
    intro j hj2 hjm
    have hj_pos : 0 < r j := hr_pos j (by omega) hjm
    have hj1_pos : 0 < r (j - 1) := hr_pos (j - 1) (by omega) (by omega)
    have hr_lt : r (j - 1) < r j := by
      have h := hr.2 (j - 1) (by omega) (by omega)
      rwa [Nat.sub_add_cancel (by omega)] at h
    have hα_j1 : 0 < α (j - 1) := hα.1 (j - 1) (by omega) (by omega)
    have hexp_j1_lt : Real.exp (-α (j - 1)) < 1 := by
      rw [Real.exp_lt_one_iff]
      linarith
    have h1 : r (j - 1) * Real.exp (-α (j - 1)) < r (j - 1) := by
      nlinarith
    have h7 : 1 - Real.exp (-α 1) = (1 - Real.exp (-α j)) / (1 - r (j - 1) / r j) :=
      hα.2.2 j hj2 hjm
    have hdenom_pos : 0 < 1 - r (j - 1) / r j := by
      rw [sub_pos, div_lt_one hj_pos]
      exact hr_lt
    have h7' : (1 - Real.exp (-α 1)) * (1 - r (j - 1) / r j) = 1 - Real.exp (-α j) := by
      rw [h7, div_mul_cancel₀ _ (ne_of_gt hdenom_pos)]
    have h7'' : (1 - Real.exp (-α 1)) * (r j - r (j - 1)) = r j - r j * Real.exp (-α j) := by
      have hdiv : (1 - r (j - 1) / r j) * r j = r j - r (j - 1) := by
        rw [sub_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt hj_pos)]
      calc
        (1 - Real.exp (-α 1)) * (r j - r (j - 1))
          = (1 - Real.exp (-α 1)) * ((1 - r (j - 1) / r j) * r j) := by rw [hdiv]
        _ = (1 - Real.exp (-α 1)) * (1 - r (j - 1) / r j) * r j := by ring
        _ = (1 - Real.exp (-α j)) * r j := by rw [h7']
        _ = r j - r j * Real.exp (-α j) := by ring
    have h2 : r (j - 1) < r j * Real.exp (-α j) := by
      have hexp1 : 0 < Real.exp (-α 1) := hexp_pos 1
      nlinarith
    have h_step : r (j - 1) * Real.exp (-α (j - 1)) < r j * Real.exp (-α j) := lt_trans h1 h2
    have hBj_eq := hB_eq B hB j (by omega) hjm
    have hBj1_eq := hB_eq B hB (j - 1) (by omega) (by omega)
    have hBj_pos : 0 < B j := hB_pos j (by omega) hjm
    have h_prod_pos : 0 < r (j - 1) * Real.exp (-α (j - 1)) := mul_pos hj1_pos (hexp_pos (j - 1))
    nlinarith
  · intro B B' hB hB' j hj1 hjm
    have h1 := hB_eq B hB j hj1 hjm
    have h2 := hB_eq B' hB' j hj1 hjm
    have hpos : 0 < r j * Real.exp (-α j) := mul_pos (hr_pos j hj1 hjm) (hexp_pos j)
    nlinarith
