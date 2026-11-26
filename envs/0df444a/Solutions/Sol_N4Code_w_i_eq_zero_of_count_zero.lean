-- Prove2me | solution 1 for N4Code.w_i_eq_zero_of_count_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:16:40.084393+00:00
-- url     : https://prove2.me/submissions/7b2a372d-238c-40ea-ab57-00ba0935321b

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_fiber_card_eq_count
import Theorems.Thm_N4Code_w_i_eq_card_onesOn


set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (i : ℕ) (y : Word n) (h : count C i = 0) :
    w_i C i y = 0 := by
  rw [w_i_eq_card_onesOn]
  have hfib : (fiber C i).card = 0 := by
    rw [fiber_card_eq_count, h]
  have hfib' : fiber C i = ∅ := Finset.card_eq_zero.mp hfib
  rw [hfib']
  simp [onesOn]
end N4Code
