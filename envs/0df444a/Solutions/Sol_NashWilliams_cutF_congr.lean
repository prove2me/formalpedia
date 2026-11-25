-- Prove2me | solution 1 for NashWilliams.cutF_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:40:49.046642+00:00
-- url     : https://prove2.me/submissions/1ec6854d-ab96-489f-a306-980c517c1228

module
public import Mathlib
public import Definitions.Def_NashWilliamsLib_Basic
public import Theorems.Thm_NashWilliams_cutF_le_of_forall

set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V]
namespace NashWilliams
theorem _root_.solution {ends : ι → V × V} {F : Finset ι} {S S' : Finset V}
    (h : ∀ i ∈ F, (((ends i).1 ∈ S) ≠ ((ends i).2 ∈ S) ↔
      ((ends i).1 ∈ S') ≠ ((ends i).2 ∈ S'))) :
    cutF ends F S = cutF ends F S' :=
  le_antisymm (cutF_le_of_forall fun i hi => (h i hi).1)
    (cutF_le_of_forall fun i hi => (h i hi).2)
end NashWilliams
