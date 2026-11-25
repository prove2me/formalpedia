-- Prove2me | solution 1 for NashWilliams.mem_erase_of_joins
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:27:26.351114+00:00
-- url     : https://prove2.me/submissions/0aa33a64-68c2-4828-acdb-b4b6e3916144

module
public import Definitions.Def_NashWilliamsLib_Mader
public import Definitions.Def_NashWilliamsLib_Splitting
public import Definitions.Def_NashWilliamsLib_Orientation

set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V] [DecidableEq ι]
omit [DecidableEq ι]
namespace NashWilliams
theorem _root_.solution {T : Finset V} {s u : V} {ends : ι → V × V} {F : Finset ι}
    (hin : Inside T ends F) {i : ι} (hi : i ∈ F) (hJ : Joins s u (ends i)) : u ∈ T.erase s := by
  obtain ⟨h1, h2⟩ := hin i hi
  obtain ⟨h | h, hus⟩ := hJ
  · rw [h] at h2; exact mem_erase.2 ⟨hus, h2⟩
  · rw [h] at h1; exact mem_erase.2 ⟨hus, h1⟩
end NashWilliams
