-- Prove2me | solution 1 for NashWilliams.joins_oth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:17:50.09865+00:00
-- url     : https://prove2.me/submissions/fb55771b-830c-4a5e-bb16-4e6a849e008a

module
public import Definitions.Def_NashWilliamsLib_Basic
public import Definitions.Def_NashWilliamsLib_Splitting

set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V]
namespace NashWilliams
theorem _root_.solution {s : V} {p : V × V} (h : (p.1 = s) ≠ (p.2 = s)) : Joins s (oth s p) p := by
  unfold Joins oth
  by_cases h1 : p.1 = s
  · have h2 : p.2 ≠ s := fun h2 => h (by simp [h1, h2])
    simp only [h1, ↓reduceIte]
    exact ⟨Or.inl (Prod.ext h1 rfl), h2⟩
  · have h2 : p.2 = s := by
      by_contra h2
      exact h (by simp [h1, h2])
    simp only [h1, ↓reduceIte]
    exact ⟨Or.inr (Prod.ext rfl h2), h1⟩
end NashWilliams
