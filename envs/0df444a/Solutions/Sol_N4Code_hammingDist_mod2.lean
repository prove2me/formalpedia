-- Prove2me | solution 1 for N4Code.hammingDist_mod2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:23:41.896945+00:00
-- url     : https://prove2.me/submissions/be82203a-3249-4637-8137-492cbd0d8df3

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_hammingWeight_xor_mod2

set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (x y z : Word n) :
    hammingDist x z % 2 = (hammingDist x y + hammingDist y z) % 2 := by
  unfold hammingDist
  have hxor : bitXor x z = bitXor (bitXor x y) (bitXor y z) := by
    funext t
    cases hx : x t <;> cases hy : y t <;> cases hz : z t <;> simp [bitXor, hx, hy, hz]
  calc
    hammingWeight (bitXor x z) % 2
        = hammingWeight (bitXor (bitXor x y) (bitXor y z)) % 2 := by rw [hxor]
    _ = (hammingWeight (bitXor x y) + hammingWeight (bitXor y z)) % 2 :=
          hammingWeight_xor_mod2 (bitXor x y) (bitXor y z)
end N4Code
