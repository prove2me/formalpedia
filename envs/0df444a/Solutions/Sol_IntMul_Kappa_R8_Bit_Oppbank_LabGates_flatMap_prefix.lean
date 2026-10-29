-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.LabGates_flatMap_prefix
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:38:49.012679+00:00
-- url     : https://prove2.me/submissions/edb4b290-2f51-48fc-a100-8647871fd410

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_LabGates_append
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank

theorem solution {Wr : Type*} [Fintype Wr] [DecidableEq Wr] {R : Type*} [CommRing R]
    {m N k : ℕ} (blk : ℕ → List (Instr Wr R m))
    (L : Wr → FMat m N)
    (h : ∀ (i : ℕ), i < k →
      LabGates N (blk i) (((List.range i).flatMap blk).foldl (labStepH N) L)) :
    LabGates N ((List.range k).flatMap blk) L := by
  induction k generalizing L with
  | zero => simp [LabGates]
  | succ k ih =>
    have hr : List.range (k + 1) = List.range k ++ [k] := by simp [List.range_succ]
    rw [hr, List.flatMap_append, List.flatMap_singleton]
    refine (LabGates_append (l₁ := (List.range k).flatMap blk) (l₂ := blk k) L).2 ⟨?_, ?_⟩
    · exact ih L (fun i hi => h i (Nat.lt_succ_of_lt hi))
    · -- foldl_append: (l1 ++ [x]).foldl = foldl on x after l1
      -- here l2 = blk k is a list, and flatMap_singleton means we append (blk k) as a list
      -- LabGates_append gives second component LabGates (blk k) (prefix.foldl labStepH L)
      simpa using h k (Nat.lt_succ_self k)
