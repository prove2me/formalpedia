-- Prove2me | solution 1 for MonoApport.Flow.proposition_8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T14:28:22.989864+00:00
-- url     : https://prove2.me/submissions/f9add836-5ccb-41c4-b42b-440db5793c4a

import Mathlib
import Definitions.Def_MonoApport_Flow_Setting

open MonoApport.Flow

theorem solution (f : Solution) (hf : IsSolution f) :
    HouseMonotone f ↔
      ∀ (n : ℕ) (p : Fin n → ℕ), IsPop p → ∀ H : ℕ, 0 < H → f p H ≤ f p (H + 1) := by
  constructor
  · intro hm n p hp H hH
    exact (hm n p hp H (H + 1) (H + 2) hH (by omega) (by omega)).1
  · intro hs n p hp H₁ H₂ H₃ h1 h12 h23
    have mono : ∀ a b : ℕ, 0 < a → a ≤ b → f p a ≤ f p b := by
      intro a b ha hab
      induction b, hab using Nat.le_induction with
      | base => exact le_rfl
      | succ b hab ih => exact ih.trans (hs n p hp b (by omega))
    exact ⟨mono _ _ h1 h12.le, mono _ _ (by omega) h23.le⟩
