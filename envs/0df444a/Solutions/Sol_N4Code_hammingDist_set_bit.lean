-- Prove2me | solution 1 for N4Code.hammingDist_set_bit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:17:03.507782+00:00
-- url     : https://prove2.me/submissions/509e1f4e-bbb9-431e-8a86-75b66e85b2fc

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_hammingDist_flip_flip

set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (x : Word n) (t : Fin n) (y : Word n) (b : Bool)
    (hx0 : x t = false) :
    hammingDist (fun u => if u = t then b else x u) y =
      if b = true then hammingDist x (flipBit t y) else hammingDist x y := by
  by_cases hb : b = true
  · have hx : (fun u : Fin n => if u = t then true else x u) = flipBit t x := by
      funext u
      by_cases ht : u = t
      · simp [flipBit, ht, hx0]
      · simp [flipBit, ht]
    rw [hb, hx, ← hammingDist_flip_flip, flipBit_involutive]
    simp
  · have hbf : b = false := by
      cases b <;> simp at hb ⊢
    have hx : (fun u : Fin n => if u = t then false else x u) = x := by
      funext u
      by_cases ht : u = t
      · simp [ht, hx0]
      · simp [ht]
    rw [hbf, hx]
    simp
end N4Code
