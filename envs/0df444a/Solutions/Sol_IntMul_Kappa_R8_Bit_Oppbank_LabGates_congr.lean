-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.LabGates_congr
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:46:49.669281+00:00
-- url     : https://prove2.me/submissions/2006617e-33a3-4f63-814f-76bdb55364c6

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192

open IntMul.Kappa.R6.Bit
open Function

private def touches {Wr : Type*} [DecidableEq Wr] {R : Type*} {m : ℕ}
    (i : Instr Wr R m) (w : Wr) : Prop :=
  match i with
  | .gate _ S => w ∈ S
  | .edge w' _ => w = w'

private theorem touches_iff {Wr : Type*} [DecidableEq Wr] {R : Type*} {m : ℕ}
    (i : Instr Wr R m) (w : Wr) :
    touches i w ↔ (match i with
      | .gate _ S => w ∈ S
      | .edge w' _ => w = w') := by
  cases i <;> simp [touches]

private theorem mem_cons_touches {Wr : Type*} [DecidableEq Wr] {R : Type*} {m : ℕ}
    {i : Instr Wr R m} {l : List (Instr Wr R m)} {w : Wr}
    (h : ∃ j ∈ l, touches j w) : ∃ j ∈ i :: l, touches j w := by
  obtain ⟨j, hj, ht⟩ := h
  exact ⟨j, List.mem_cons_of_mem i hj, ht⟩

private theorem LabGates_congr_touches {Wr : Type*} [Fintype Wr] [DecidableEq Wr]
    {R : Type*} [CommRing R] {m N : ℕ} :
    ∀ (l : List (Instr Wr R m)) (L L' : Wr → FMat m N),
      (∀ w, (∃ i ∈ l, touches i w) → L w = L' w) →
      (LabGates N l L ↔ LabGates N l L') := by
  intro l
  induction l with
  | nil =>
    intro L L' _
    simp [LabGates]
  | cons i rest ih =>
    intro L L' h
    cases i with
    | gate g S =>
      have hrest : ∀ w, (∃ j ∈ rest, touches j w) → L w = L' w :=
        fun w hw => h w (mem_cons_touches hw)
      constructor
      · intro hL
        constructor
        · intro w hw w' hw'
          have ew : L w = L' w :=
            h w ⟨Instr.gate g S, List.Mem.head _, by simpa [touches] using hw⟩
          have ew' : L w' = L' w' :=
            h w' ⟨Instr.gate g S, List.Mem.head _, by simpa [touches] using hw'⟩
          exact ew.symm.trans (hL.1 w hw w' hw' |>.trans ew')
        · exact (ih L L' hrest).1 (by simpa [labStepH] using hL.2)
      · intro hL'
        constructor
        · intro w hw w' hw'
          have ew : L w = L' w :=
            h w ⟨Instr.gate g S, List.Mem.head _, by simpa [touches] using hw⟩
          have ew' : L w' = L' w' :=
            h w' ⟨Instr.gate g S, List.Mem.head _, by simpa [touches] using hw'⟩
          exact ew.trans (hL'.1 w hw w' hw' |>.trans ew'.symm)
        · exact (ih L L' hrest).2 (by simpa [labStepH] using hL'.2)
    | edge wed e =>
      constructor
      · intro hL
        refine ⟨trivial, ?_⟩
        set L1 := labStepH (R := R) N L (Instr.edge wed e) with hL1
        set L1' := labStepH (R := R) N L' (Instr.edge wed e) with hL1'
        have hagree : ∀ w, (∃ j ∈ rest, touches j w) → L1 w = L1' w := by
          intro w hw
          rw [hL1, hL1']
          change update L wed (edgeMat N e * L wed) w =
            update L' wed (edgeMat N e * L' wed) w
          by_cases hwe : w = wed
          · have heq : L wed = L' wed :=
              h wed ⟨Instr.edge wed e, List.Mem.head _, rfl⟩
            rw [hwe, update_self, update_self, heq]
          · rw [update_of_ne hwe, update_of_ne hwe]
            exact h w (mem_cons_touches hw)
        exact (ih L1 L1' hagree).1 hL.2
      · intro hL'
        refine ⟨trivial, ?_⟩
        set L1 := labStepH (R := R) N L (Instr.edge wed e) with hL1
        set L1' := labStepH (R := R) N L' (Instr.edge wed e) with hL1'
        have hagree : ∀ w, (∃ j ∈ rest, touches j w) → L1 w = L1' w := by
          intro w hw
          rw [hL1, hL1']
          change update L wed (edgeMat N e * L wed) w =
            update L' wed (edgeMat N e * L' wed) w
          by_cases hwe : w = wed
          · have heq : L wed = L' wed :=
              h wed ⟨Instr.edge wed e, List.Mem.head _, rfl⟩
            rw [hwe, update_self, update_self, heq]
          · rw [update_of_ne hwe, update_of_ne hwe]
            exact h w (mem_cons_touches hw)
        exact (ih L1 L1' hagree).2 hL'.2

theorem solution {Wr : Type*} [Fintype Wr] [DecidableEq Wr] {R : Type*} [CommRing R]
    {m N : ℕ} (l : List (Instr Wr R m)) (L L' : Wr → FMat m N)
    (h : ∀ w, (∃ i ∈ l,
      match i with
      | .gate _ S => w ∈ S
      | .edge w' _ => w = w') → L w = L' w) :
    LabGates N l L ↔ LabGates N l L' := by
  refine LabGates_congr_touches l L L' ?_
  intro w hw
  obtain ⟨i, hi, ht⟩ := hw
  exact h w ⟨i, hi, (touches_iff i w).1 ht⟩
