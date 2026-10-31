-- Prove2me | solution 1 for MNatOps.Monotone.thm3_first_half
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T09:43:37.284214+00:00
-- url     : https://prove2.me/submissions/97329a95-5376-4c67-aaa6-20f72b1897f8

import Mathlib
import Definitions.Def_MNatOps_Monotone_Model
import Theorems.Thm_MNatOps_Monotone_thm3_induction

open MNatOps.Monotone in
theorem solution {m n : ℕ} (G : (Fin m ⊕ Fin n → ℤ) → WithBot ℝ) (hG : SSQMNatConcave G)
    (l : Fin n → WithBot ℤ) (u : Fin n → WithTop ℤ) (s s' : Fin m → ℤ) (hss : s ≤ s')
    (a : Fin n → ℤ) (ha : a ∈ optSet G l u s) (haf : G (Sum.elim s a) ≠ ⊥)
    (hs' : s' ∈ finiteParams G l u) :
    ∃ a'' ∈ optSet G l u s', a'' ≤ a := by
  obtain ⟨a'', h1, h2⟩ := thm3_induction G hG l u s s' hss a ha haf hs' n le_rfl
  exact ⟨a'', h1, fun k => h2 k k.isLt⟩
