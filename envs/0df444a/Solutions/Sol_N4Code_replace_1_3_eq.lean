-- Prove2me | solution 1 for N4Code.replace_1_3_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:04:10.582753+00:00
-- url     : https://prove2.me/submissions/44f97233-fc0c-4fc6-984a-b7bda7a998be

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare

set_option autoImplicit true
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C C' : Code n) (t : Fin n) (hcol' : C' t = col3)
    (hsame : ∀ u : Fin n, u ≠ t → C' u = C u) :
    C' = replaceColumn C t col3 := by
  funext u
  by_cases hu : u = t <;> simp [replaceColumn, hu, hcol', hsame]
end N4Code
