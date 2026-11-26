-- Prove2me | solution 1 for N4Code.w_i_le_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:16:51.952464+00:00
-- url     : https://prove2.me/submissions/2be9a2ec-3222-447d-b3fb-53674e974ff5

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
theorem _root_.solution {n : ℕ} (C : Code n) (i : ℕ) (y : Word n) : w_i C i y ≤ count C i := by
  rw [w_i_eq_card_onesOn]
  exact le_trans (Finset.card_le_card (by
    intro t ht
    exact (Finset.mem_filter.mp ht).1)) (le_of_eq (fiber_card_eq_count C i))
end N4Code
