-- Prove2me | solution 1 for N4Code.classI_count1_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:02:30.064877+00:00
-- url     : https://prove2.me/submissions/c4ef1179-8441-419c-9a16-fe8ba2a164ed

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
theorem _root_.solution {n : ℕ} (C : Code n) (h : ClassI C) : count C 1 > 0 := by
  rcases h.1 with ⟨k, hk⟩
  omega
end N4Code
