-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.LabGates_flatMap_range
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:34:16.741828+00:00
-- url     : https://prove2.me/submissions/66d3a837-1e40-4ce5-8faa-4879499f210a

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192

open IntMul.Kappa.R6.Bit

private theorem LabGates_append' {Wr : Type*} [Fintype Wr] [DecidableEq Wr] {R : Type*} [CommRing R]
    {m N : ℕ} (l₁ l₂ : List (Instr Wr R m)) (L : Wr → FMat m N) :
    LabGates N (l₁ ++ l₂) L ↔
      LabGates N l₁ L ∧ LabGates N l₂ (l₁.foldl (labStepH N) L) := by
  induction l₁ generalizing L with
  | nil => simp [LabGates]
  | cons i l ih =>
    cases i with
    | gate g S =>
      constructor
      · intro h
        refine ⟨⟨h.1, (ih _).1 h.2 |>.1⟩, (ih _).1 h.2 |>.2⟩
      · intro h
        have := (ih (labStepH N L (.gate g S))).2 ⟨h.1.2, by simpa [List.foldl_cons] using h.2⟩
        exact ⟨h.1.1, this⟩
    | edge w e =>
      constructor
      · intro h
        refine ⟨⟨trivial, (ih _).1 h.2 |>.1⟩, (ih _).1 h.2 |>.2⟩
      · intro h
        have := (ih (labStepH N L (.edge w e))).2 ⟨h.1.2, by simpa [List.foldl_cons] using h.2⟩
        exact ⟨trivial, this⟩

theorem solution {Wr : Type*} [Fintype Wr] [DecidableEq Wr] {R : Type*} [CommRing R]
    {m N k : ℕ} (blk : ℕ → List (Instr Wr R m))
    (L : Wr → FMat m N)
    (h : ∀ (i : ℕ), i < k → ∀ L', LabGates N (blk i) L') :
    LabGates N ((List.range k).flatMap blk) L := by
  induction k generalizing L with
  | zero => simp [LabGates]
  | succ k ih =>
    -- range (k+1) = range k ++ [k]
    have hr : List.range (k + 1) = List.range k ++ [k] := by
      simp [List.range_succ]
    rw [hr, List.flatMap_append, List.flatMap_singleton]
    refine (LabGates_append' _ _ L).2 ⟨ih L (fun i hi L' => h i (Nat.lt_succ_of_lt hi) L'), ?_⟩
    exact h k (Nat.lt_succ_self k) _
