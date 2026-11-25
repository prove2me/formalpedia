-- Prove2me | solution 1 for NashWilliams.outCutF_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:23:05.588863+00:00
-- url     : https://prove2.me/submissions/fd980dfc-2286-4da3-846d-e33a15856b16

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
theorem _root_.solution (ends : ι → V × V) (o : ι → Bool) (F : Finset ι) (S : Finset V) :
    outCutF ends o F S = ∑ i ∈ F, lv (ends i) (o i) S := by
  unfold outCutF lv
  rw [Finset.card_filter]
end NashWilliams
