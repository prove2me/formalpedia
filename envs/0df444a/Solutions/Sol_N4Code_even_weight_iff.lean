-- Prove2me | solution 1 for N4Code.even_weight_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:01:59.908596+00:00
-- url     : https://prove2.me/submissions/816d9c21-64fa-4304-820c-e6c21501776b

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
theorem _root_.solution {a b : ℕ} (h : b = a ∨ b = 4 - a) (ha4 : a ≤ 4) (hb4 : b ≤ 4) :
    Even b ↔ Even a := by
  constructor
  · intro hb
    rcases h with h | h
    · simpa [h] using hb
    · rcases hb with ⟨k, hk⟩
      refine ⟨2 - k, ?_⟩
      omega
  · intro ha
    rcases h with h | h
    · simpa [h] using ha
    · rcases ha with ⟨k, hk⟩
      refine ⟨2 - k, ?_⟩
      omega
end N4Code
