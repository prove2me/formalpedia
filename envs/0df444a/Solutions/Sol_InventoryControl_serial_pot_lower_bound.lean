-- Prove2me | solution 1 for InventoryControl.serial_pot_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-27T17:01:23.886738+00:00
-- url     : https://prove2.me/submissions/31448c2a-44f3-434b-830b-1d5ba0a42ea5

import Mathlib
import Definitions.Def_InventoryControl_serial

open InventoryControl in
theorem solution {N : ℕ} (A e : Fin N → ℝ) (d : ℝ) (Qrel : Fin N → ℝ)
    (hopt : ∀ Q : Fin N → ℝ, (∀ i, 0 < Q i) → SerialNested Q →
      serialCost A e d Qrel ≤ serialCost A e d Q)
    (Q : Fin N → ℝ) (hpos : ∀ i, 0 < Q i) (hpot : SerialPowerOfTwo Q) :
    SerialNested Q ∧ serialCost A e d Qrel ≤ serialCost A e d Q := by
  have hnest : SerialNested Q := by
    intro i j hij
    obtain ⟨k, hk⟩ := hpot i j hij
    rw [hk]
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
    have h2 : 0 < Q i := hpos i
    nlinarith
  exact ⟨hnest, hopt Q hpos hnest⟩
