-- Prove2me | solution 1 for N4Code.testBit2_of_le7
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:23:05.976714+00:00
-- url     : https://prove2.me/submissions/9fcbfec4-3755-4db7-8345-0d5520dfb5b0

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
theorem _root_.solution (n : ℕ) (hn : n ≤ 7) :
    (n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7) ↔ n.testBit 2 = true := by
  have hk : ∃ k : Fin 8, (k : ℕ) = n := ⟨⟨n, by omega⟩, rfl⟩
  rcases hk with ⟨k, hk⟩
  subst n
  fin_cases k <;> decide
end N4Code
