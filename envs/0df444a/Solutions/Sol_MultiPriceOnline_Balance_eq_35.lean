-- Prove2me | solution 1 for MultiPriceOnline.Balance.eq_35
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:12:58.445967+00:00
-- url     : https://prove2.me/submissions/0800458c-592f-4ffb-91f6-7cc4fdc61e4f

import Mathlib
import Definitions.Def_MultiPriceOnline_Balance_PriceSet

set_option autoImplicit false
open MultiPriceOnline.Balance

theorem solution (m : ℕ) (r α : ℕ → ℝ) (hr : IsPriceSet m r) (hα : IsBookingLimits m r α) :
    ∀ j, 2 ≤ j → j ≤ m → r (j - 1) / r j ≤ Real.exp (-α j) := by
  intro j hj2 hjm
  obtain ⟨hr1, hrmono⟩ := hr
  obtain ⟨hαpos, _, h7⟩ := hα
  have hpos : ∀ i, 1 ≤ i → i ≤ m → 0 < r i := by
    intro i hi him
    induction i, hi using Nat.le_induction with
    | base => exact hr1
    | succ i hi ih =>
      have := hrmono i hi (by omega)
      have := ih (by omega)
      linarith
  have hlt : r (j - 1) < r j := by
    have := hrmono (j - 1) (by omega) (by omega)
    rwa [show j - 1 + 1 = j by omega] at this
  have hrj : 0 < r j := hpos j (by omega) hjm
  have hrj1 : 0 < r (j - 1) := hpos (j - 1) (by omega) (by omega)
  have hρ0 : 0 < r (j - 1) / r j := div_pos hrj1 hrj
  have hρ1 : r (j - 1) / r j < 1 := (div_lt_one hrj).2 hlt
  have h1ρ : 0 < 1 - r (j - 1) / r j := by linarith
  have e := h7 j hj2 hjm
  rw [eq_div_iff h1ρ.ne'] at e
  have hF : 1 - Real.exp (-α 1) < 1 := by
    have := Real.exp_pos (-α 1); linarith
  have hlt2 : 1 - Real.exp (-α j) < 1 - r (j - 1) / r j := by
    rw [← e]
    nlinarith
  linarith
