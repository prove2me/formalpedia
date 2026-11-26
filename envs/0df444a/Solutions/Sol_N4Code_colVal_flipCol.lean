-- Prove2me | solution 1 for N4Code.colVal_flipCol
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:25:18.165722+00:00
-- url     : https://prove2.me/submissions/181d1e18-eaf3-4bd0-8fe8-04d451850897

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
theorem _root_.solution (c : Column) : colVal (flipCol c) = 15 - colVal c := by
  have hsum : colVal (flipCol c) + colVal c = 15 := by
    unfold colVal flipCol
    rw [← Finset.sum_add_distrib]
    have hterm : ∀ j : Fin 4,
        (if !(c j) then 2 ^ (3 - j.val) else 0) + (if c j then 2 ^ (3 - j.val) else 0) =
          2 ^ (3 - j.val) := by
      intro j
      cases c j <;> simp
    rw [Finset.sum_congr rfl (fun j _ => hterm j)]
    have hsum15 : (∑ j : Fin 4, 2 ^ (3 - j.val)) = 15 := by decide
    rw [hsum15]
  have hle : colVal c ≤ 15 := colVal_le_15 c
  omega
end N4Code
