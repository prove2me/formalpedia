-- Prove2me | solution 1 for N4Code.hammingDist_flip_flip
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:16:25.25255+00:00
-- url     : https://prove2.me/submissions/4b184837-7bd7-4cb1-946b-ebfa35f2de26

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
theorem _root_.solution {n : ℕ} (x y : Word n) (t : Fin n) :
    hammingDist (flipBit t x) (flipBit t y) = hammingDist x y := by
  unfold hammingDist
  congr 1
  funext u
  by_cases ht : u = t <;> simp [bitXor, flipBit, ht]
end N4Code
