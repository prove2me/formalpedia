-- Prove2me | solution 1 for NashWilliams.outCut_eq_outCutF
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:28:33.126478+00:00
-- url     : https://prove2.me/submissions/c51dc304-010a-4e13-9f07-7f52f4f0232e

module
public import Mathlib
public import Definitions.Def_NashWilliamsLib_Orientation
public import Definitions.Def_NashWilliamsLib_Defs

set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
omit [Fintype V]
namespace NashWilliams
theorem _root_.solution (ends : ι → V × V) (o : ι → Bool) (S : Finset V) :
    outCut ends o S = outCutF ends o Finset.univ S := by
  unfold outCut outCutF
  congr 1
  ext i
  rw [mem_filter, mem_filter]
  rfl
end NashWilliams
