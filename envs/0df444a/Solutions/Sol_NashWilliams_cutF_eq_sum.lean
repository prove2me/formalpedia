-- Prove2me | solution 1 for NashWilliams.cutF_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:50:13.277654+00:00
-- url     : https://prove2.me/submissions/d41622fa-78cf-468a-a6b0-2b8222f604e1

module
public import Mathlib
public import Definitions.Def_NashWilliamsLib_Basic

set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V]
namespace NashWilliams
theorem _root_.solution (ends : ι → V × V) (F : Finset ι) (S : Finset V) :
    cutF ends F S = ∑ i ∈ F, cr (ends i) S := by
  simp [cutF, cr, Finset.card_filter]
end NashWilliams
