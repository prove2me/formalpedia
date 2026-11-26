-- Prove2me | solution 1 for N4Code.universalBetter_trans
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:09:00.624919+00:00
-- url     : https://prove2.me/submissions/eaa57aef-3f85-4323-9378-e8ba7cbcd105

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
theorem _root_.solution {n : ℕ} {A B C : Code n} (hAB : UniversalBetter A B)
    (hBC : UniversalBetter B C) : UniversalBetter A C := by
  intro ε h0 h1
  exact le_trans (hBC ε h0 h1) (hAB ε h0 h1)
end N4Code
