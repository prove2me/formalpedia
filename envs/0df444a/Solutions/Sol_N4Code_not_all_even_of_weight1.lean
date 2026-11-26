-- Prove2me | solution 1 for N4Code.not_all_even_of_weight1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:02:25.936161+00:00
-- url     : https://prove2.me/submissions/3ed44316-1775-4c00-b543-94c7351ccec0

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
theorem _root_.solution {n : ℕ} (C : Code n) (h : ∃ t : Fin n, colWeight (C t) = 1) :
    ¬ allEvenWeights C := by
  rintro hE
  rcases h with ⟨t, ht⟩
  have : Even (colWeight (C t)) := hE t
  rw [ht] at this
  rcases this with ⟨k, hk⟩
  omega
end N4Code
