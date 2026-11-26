-- Prove2me | solution 1 for N4Code.hammingWeight_xor_mod2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:23:05.182245+00:00
-- url     : https://prove2.me/submissions/962c0162-14a2-4b1f-bec5-29cf60d89dd8

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_sum_mod_two

set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (x y : Word n) :
    hammingWeight (bitXor x y) % 2 = (hammingWeight x + hammingWeight y) % 2 := by
  unfold hammingWeight
  calc
    (∑ t : Fin n, if bitXor x y t = true then 1 else 0) % 2
        = (∑ t : Fin n, (if bitXor x y t = true then 1 else 0) % 2) % 2 := sum_mod_two _ _
    _ = (∑ t : Fin n, ((if x t = true then 1 else 0) + (if y t = true then 1 else 0)) % 2) % 2 := by
          congr 1
          apply Finset.sum_congr rfl
          intro t _
          cases hx : x t <;> cases hy : y t <;> simp [bitXor, hx, hy]
    _ = (∑ t : Fin n, ((if x t = true then 1 else 0) + (if y t = true then 1 else 0))) % 2 := (sum_mod_two _ _).symm
    _ = ((∑ t : Fin n, if x t = true then 1 else 0) + (∑ t : Fin n, if y t = true then 1 else 0)) % 2 := by
          rw [Finset.sum_add_distrib]
end N4Code
