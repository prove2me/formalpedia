-- Prove2me | solution 1 for N4Code.notC0_normalize
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:23:55.077233+00:00
-- url     : https://prove2.me/submissions/87403995-fced-4628-a9b5-a862dc6b6fab

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_Equivalent_normalize

set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (i j : Fin 4)
    (hC0 : ¬ ∃ C0 : Code n, Equivalent C C0 ∧ C0form C0) :
    ¬ C0form (normalizeCode C i j) := by
  intro h
  exact hC0 ⟨normalizeCode C i j, Equivalent_normalize C i j, h⟩
end N4Code
