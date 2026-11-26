-- Prove2me | solution 1 for N4Code.even_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:30:58.474706+00:00
-- url     : https://prove2.me/submissions/9305cef8-b3e3-4b6c-a167-7fcf52016b52

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn

set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (h : Even n) : ∃ k : ℕ, n = 2 * k := by
  rcases h with ⟨k, hk⟩
  exact ⟨k, by rw [hk, two_mul]⟩
end N4Code
