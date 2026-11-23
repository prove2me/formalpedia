-- Prove2me | solution 1 for MultiAccessLogspace.Halting.lemma_3_5
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:34:12.988982+00:00
-- url     : https://prove2.me/submissions/9a5537d8-867f-41d4-9067-e22896c98bdd

import Mathlib
import Definitions.Def_MultiAccessLogspace_Halting_Rulers

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open MultiAccessLogspace.Halting

private lemma length_intercalate_singleton (a : ℕ) (blocks : List (List ℕ)) :
    (List.intercalate [a] blocks).length =
      (blocks.map List.length).sum + (blocks.length - 1) := by
  induction blocks with
  | nil => simp [List.intercalate]
  | cons B blocks ih =>
      cases blocks with
      | nil => simp [List.intercalate]
      | cons C blocks =>
          change (B ++ ([a] ++ List.intercalate [a] (C :: blocks))).length = _
          rw [List.length_append, List.length_append, ih]
          simp only [List.length_nil, List.length_singleton, List.map_cons, List.sum_cons,
            List.length_cons]
          omega

theorem solution (d b : ℕ) (hb : 1 ≤ b) (h : List ℕ) (hh : IsHyporuler b d h) :
    h.length ≤ b ^ d - 1 := by
  induction d generalizing h with
  | zero =>
      have hnil : h = [] := hh
      simp [hnil]
  | succ d ih =>
      rcases hh with ⟨blocks, hne, hlen, hblocks, rfl⟩
      have hpow : 1 ≤ b ^ d := one_le_pow₀ hb
      have hsum : (blocks.map List.length).sum ≤ blocks.length * (b ^ d - 1) := by
        calc
          (blocks.map List.length).sum ≤ (blocks.map (fun _ : List ℕ => b ^ d - 1)).sum := by
            exact List.sum_le_sum (fun B hB => ih B (hblocks B hB))
          _ = blocks.length * (b ^ d - 1) := by simp
      have hk : 1 ≤ blocks.length := by
        cases blocks with
        | nil => contradiction
        | cons B blocks => simp
      have hmul : blocks.length * (b ^ d - 1) ≤ b * (b ^ d - 1) :=
        Nat.mul_le_mul_right (b ^ d - 1) hlen
      have hmulsub : b * (b ^ d - 1) = b * b ^ d - b := by
        rw [Nat.mul_sub_left_distrib, Nat.mul_one]
      have hle : b ≤ b * b ^ d := by
        simpa using Nat.mul_le_mul_left b hpow
      have key : b ^ (d + 1) - 1 = (b - 1) + b * (b ^ d - 1) := by
        rw [pow_succ, Nat.mul_comm (b ^ d) b, hmulsub]
        omega
      rw [length_intercalate_singleton, key]
      omega
