-- Prove2me | solution 1 for NashWilliams.reachable_closed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:51:10.919829+00:00
-- url     : https://prove2.me/submissions/fa84474f-2690-49e7-83c0-32dbec451a4c

module
public import Mathlib
public import Definitions.Def_TreePackingLib_NashWilliamsAux

set_option autoImplicit true
@[expose] public section
public section
open Finset Fintype SimpleGraph Function
open NashWilliams
variable {V : Type*}
namespace NashWilliams
theorem _root_.solution {A : SimpleGraph V} (P : V → Prop) (h : ∀ a b, A.Adj a b → P a → P b)
    {a b : V} (hab : A.Reachable a b) (ha : P a) : P b := by
  obtain ⟨p⟩ := hab
  induction p with
  | nil => exact ha
  | cons hadj _ ih => exact ih (h _ _ hadj ha)
end NashWilliams
