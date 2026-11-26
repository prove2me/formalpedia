-- Prove2me | solution 1 for N4Code.count_pos_iff_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:02:11.255846+00:00
-- url     : https://prove2.me/submissions/927c97db-d8a1-435d-873f-375d65b889a0

import Definitions.Def_N4Code_Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_Performance

set_option autoImplicit true
open scoped BigOperators
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (i : ℕ) :
    count C i > 0 ↔ ∃ t : Fin n, colVal (C t) = i := by
  constructor
  · intro h
    by_contra hn
    have hz : count C i = 0 := by
      unfold count
      apply Finset.sum_eq_zero
      intro t _
      have : colVal (C t) ≠ i := by
        intro hti
        exact hn ⟨t, hti⟩
      simp [this]
    omega
  · rintro ⟨t, ht⟩
    by_contra hn
    have hz : count C i = 0 := by omega
    have hz' : ∀ t' : Fin n, colVal (C t') ≠ i := by
      simpa [count] using hz
    exact hz' t ht
end N4Code
