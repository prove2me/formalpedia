-- Prove2me | solution 1 for N4Code.dRow_flip_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:16:20.522865+00:00
-- url     : https://prove2.me/submissions/a6b79a5f-8395-42b0-8c96-1620ccc1e03d

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_dRow_eq_hammingDist


set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) (hcol : C t = col0) :
    ∀ i : Fin 4, (y t = true → dRow C i (flipBit t y) = dRow C i y - 1) ∧
      (y t = false → dRow C i (flipBit t y) = dRow C i y + 1) := by
  intro i
  rw [dRow_eq_hammingDist, dRow_eq_hammingDist]
  have ht0 : (row C i) t = false := by
    unfold row
    simp [hcol, colBit, col0]
  constructor
  · intro hyt
    unfold hammingDist hammingWeight
    have hsplit_new := sum_split_at
      (fun u : Fin n => if bitXor (row C i) (flipBit t y) u = true then 1 else 0) t
    have hsplit_old := sum_split_at
      (fun u : Fin n => if bitXor (row C i) y u = true then 1 else 0) t
    have hS : (∑ u ∈ (Finset.univ.erase t),
        if bitXor (row C i) (flipBit t y) u = true then 1 else 0) =
        ∑ u ∈ (Finset.univ.erase t), if bitXor (row C i) y u = true then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      have ht : u ≠ t := (Finset.mem_erase.mp hu).1
      simp [bitXor, flipBit, ht]
    have htnew : (if bitXor (row C i) (flipBit t y) t = true then 1 else 0) = 0 := by
      have : bitXor (row C i) (flipBit t y) t = false := by
        simp [bitXor, flipBit, ht0, hyt]
      simp [this]
    have htold : (if bitXor (row C i) y t = true then 1 else 0) = 1 := by
      have : bitXor (row C i) y t = true := by
        simp [bitXor, ht0, hyt]
      simp [this]
    rw [hsplit_new, hsplit_old, hS, htnew, htold]
    omega
  · intro hyt
    unfold hammingDist hammingWeight
    have hsplit_new := sum_split_at
      (fun u : Fin n => if bitXor (row C i) (flipBit t y) u = true then 1 else 0) t
    have hsplit_old := sum_split_at
      (fun u : Fin n => if bitXor (row C i) y u = true then 1 else 0) t
    have hS : (∑ u ∈ (Finset.univ.erase t),
        if bitXor (row C i) (flipBit t y) u = true then 1 else 0) =
        ∑ u ∈ (Finset.univ.erase t), if bitXor (row C i) y u = true then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      have ht : u ≠ t := (Finset.mem_erase.mp hu).1
      simp [bitXor, flipBit, ht]
    have htnew : (if bitXor (row C i) (flipBit t y) t = true then 1 else 0) = 1 := by
      have : bitXor (row C i) (flipBit t y) t = true := by
        simp [bitXor, flipBit, ht0, hyt]
      simp [this]
    have htold : (if bitXor (row C i) y t = true then 1 else 0) = 0 := by
      have : bitXor (row C i) y t = false := by
        simp [bitXor, ht0, hyt]
      simp [this]
    rw [hsplit_new, hsplit_old, hS, htnew, htold]
end N4Code
