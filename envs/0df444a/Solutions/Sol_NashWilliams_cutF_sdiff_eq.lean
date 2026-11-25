-- Prove2me | solution 1 for NashWilliams.cutF_sdiff_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:42:17.646333+00:00
-- url     : https://prove2.me/submissions/351ea1c5-3360-4b47-b3cb-113013412994

module
public import Mathlib
public import Definitions.Def_NashWilliamsLib_Basic
public import Theorems.Thm_NashWilliams_cutF_congr

set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V]
namespace NashWilliams
theorem _root_.solution {T : Finset V} {ends : ι → V × V} {F : Finset ι} (hin : Inside T ends F)
    (S : Finset V) : cutF ends F (T \ S) = cutF ends F S := by
  refine cutF_congr fun i hi => ?_
  obtain ⟨h1, h2⟩ := hin i hi
  by_cases h3 : (ends i).1 ∈ S <;> by_cases h4 : (ends i).2 ∈ S <;> simp [*]
end NashWilliams
