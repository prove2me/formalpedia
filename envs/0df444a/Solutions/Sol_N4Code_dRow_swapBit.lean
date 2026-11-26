-- Prove2me | solution 1 for N4Code.dRow_swapBit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:25:23.961356+00:00
-- url     : https://prove2.me/submissions/07e8bb17-b7a1-4f14-9115-385525ac0503

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_hammingWeight_swapBits

set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (j : Fin 4) (t₁ t' : Fin n)
    (h1 : C t₁ = col0) (h' : C t' = col0) (y : Word n) :
    dRow C j (swapBits t₁ t' y) = dRow C j y := by
  unfold dRow hammingDist
  have hxor : bitXor (row C j) (swapBits t₁ t' y) = swapBits t₁ t' (bitXor (row C j) y) := by
    funext u
    by_cases hu₁ : u = t₁ <;> by_cases hut : u = t' <;>
      simp [swapBits, bitXor, row, colBit, col0, h1, h', hu₁, hut]
  calc
    dRow C j (swapBits t₁ t' y) = hammingWeight (bitXor (row C j) (swapBits t₁ t' y)) := rfl
    _ = hammingWeight (swapBits t₁ t' (bitXor (row C j) y)) := by rw [hxor]
    _ = hammingWeight (bitXor (row C j) y) := hammingWeight_swapBits t₁ t' (bitXor (row C j) y)
    _ = dRow C j y := rfl
end N4Code
