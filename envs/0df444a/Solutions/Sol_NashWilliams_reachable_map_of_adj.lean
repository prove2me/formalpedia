-- Prove2me | solution 1 for NashWilliams.reachable_map_of_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:40:59.022069+00:00
-- url     : https://prove2.me/submissions/c0312891-dddf-4eb1-8125-22b8c2c55237

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
theorem _root_.solution {W : Type*} {A : SimpleGraph V} {B : SimpleGraph W} (g : V → W)
    (h : ∀ a b, A.Adj a b → B.Reachable (g a) (g b)) {a b : V} (hab : A.Reachable a b) :
    B.Reachable (g a) (g b) := by
  obtain ⟨p⟩ := hab
  induction p with
  | nil => rfl
  | cons hadj _ ih => exact (h _ _ hadj).trans ih
end NashWilliams
