-- Prove2me | solution 1 for MNatOps.Monotone.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T09:45:45.343866+00:00
-- url     : https://prove2.me/submissions/a8bf12db-43c6-4e64-875b-394a815aab1e

import Mathlib
import Definitions.Def_MNatOps_Monotone_Model
import Theorems.Thm_MNatOps_Monotone_thm3_first_half
import Theorems.Thm_MNatOps_Monotone_thm3_second_half

open MNatOps.Monotone in
theorem solution {m n : ℕ} (G : (Fin m ⊕ Fin n → ℤ) → WithBot ℝ) (hG : SSQMNatConcave G)
    (l : Fin n → WithBot ℤ) (u : Fin n → WithTop ℤ) (hlu : BoxNonempty l u) :
    IsNonincreasingOn (optSet G l u) (finiteParams G l u) := by
  -- every optimal solution at a parameter in S has finite value
  have hfin : ∀ s ∈ finiteParams G l u, ∀ a ∈ optSet G l u s, G (Sum.elim s a) ≠ ⊥ := by
    rintro s ⟨b, hb, hbf⟩ a ha h
    have := ha.2 b hb.1
    rw [h] at this
    exact hbf (le_bot_iff.mp this)
  intro s hs s' hs' hss
  exact ⟨fun a ha => thm3_first_half G hG l u s s' hss a ha (hfin s hs a ha) hs',
    fun a' ha' => thm3_second_half G hG l u s s' hss hs a' ha' (hfin s' hs' a' ha')⟩
