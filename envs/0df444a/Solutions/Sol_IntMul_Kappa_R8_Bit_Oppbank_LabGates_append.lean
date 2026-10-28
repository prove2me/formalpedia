-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.LabGates_append
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:28:14.538472+00:00
-- url     : https://prove2.me/submissions/992314a3-f0d3-4d91-b70f-d63fdf611ebc

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa.R6.Bit

theorem solution {Wr : Type*} [Fintype Wr] [DecidableEq Wr] {R : Type*} [CommRing R]
    {m N : ℕ} (l₁ l₂ : List (Instr Wr R m))
    (L : Wr → FMat m N) :
    LabGates N (l₁ ++ l₂) L ↔
      LabGates N l₁ L ∧ LabGates N l₂ (l₁.foldl (labStepH N) L) := by
  induction l₁ generalizing L with
  | nil =>
    simp [LabGates]
  | cons i l ih =>
    cases i with
    | gate g S =>
      constructor
      · intro h
        -- h : LabGates (gate::l ++ l2) L = (gate cond ∧ LabGates (l++l2) (labStepH L gate))
        refine ⟨⟨h.1, (ih _).1 h.2 |>.1⟩, (ih _).1 h.2 |>.2⟩
      · intro h
        -- h.1 : LabGates (gate::l) L = (cond ∧ LabGates l ...)
        -- h.2 : LabGates l2 (foldl (gate::l) L)
        have := (ih (labStepH N L (.gate g S))).2 ⟨h.1.2, by
          simpa [List.foldl_cons] using h.2⟩
        exact ⟨h.1.1, this⟩
    | edge w e =>
      constructor
      · intro h
        refine ⟨⟨trivial, (ih _).1 h.2 |>.1⟩, (ih _).1 h.2 |>.2⟩
      · intro h
        have := (ih (labStepH N L (.edge w e))).2 ⟨h.1.2, by
          simpa [List.foldl_cons] using h.2⟩
        exact ⟨trivial, this⟩
