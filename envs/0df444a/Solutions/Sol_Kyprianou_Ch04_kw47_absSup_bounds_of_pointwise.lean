-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_absSup_bounds_of_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T12:15:17.279018+00:00
-- url     : https://prove2.me/submissions/b3ebab5e-bddb-4a60-a1e9-1c67f8aa77cd

import Mathlib
open Set
open scoped NNReal
set_option autoImplicit false

theorem solution
    (f : NNReal → Real) (t : NNReal) (B : Real)
    (hb : ∀ s : NNReal, s ≤ t → |f s| ≤ B) :
    0 ≤ sSup ((fun s : NNReal => |f s|) '' Iic t) ∧
    sSup ((fun s : NNReal => |f s|) '' Iic t) ≤ B := by 
  let A := (fun s : NNReal => |f s|) '' Iic t
  have hB : BddAbove A := ⟨B, by rintro x ⟨s, hs, rfl⟩; exact hb s hs⟩
  have h0 : |f t| ∈ A := ⟨t, Set.mem_Iic.mpr le_rfl, rfl⟩
  exact ⟨(abs_nonneg _).trans (le_csSup hB h0),
    csSup_le ⟨_, h0⟩ (by rintro x ⟨s, hs, rfl⟩; exact hb s hs)⟩
