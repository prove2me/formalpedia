-- Prove2me | solution 1 for NashWilliams.dsF_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:55:04.992967+00:00
-- url     : https://prove2.me/submissions/c399d639-d89b-466e-b0e1-5e003732e411

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
theorem _root_.solution (s : V) (ends : ι → V × V) (F : Finset ι) (X : Finset V) :
    dsF s ends F X = ∑ l ∈ F, jn s (ends l) X := by
  unfold dsF jn
  rw [Finset.card_filter]
end NashWilliams
