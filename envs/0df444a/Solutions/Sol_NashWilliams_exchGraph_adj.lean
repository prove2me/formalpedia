-- Prove2me | solution 1 for NashWilliams.exchGraph_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:50:54.145811+00:00
-- url     : https://prove2.me/submissions/d8508304-c83e-42e8-a493-ebc546ef3a35

module
public import Mathlib
public import Definitions.Def_TreePackingLib_NashWilliamsAux

set_option autoImplicit true
@[expose] public section
public section
open Finset Fintype SimpleGraph Function
open NashWilliams
variable {V : Type*}
variable {G : SimpleGraph V} {k : ℕ}
namespace NashWilliams
theorem _root_.solution {F₀ : Fin k → SimpleGraph V} {a b : V} :
    (exchGraph G F₀).Adj a b ↔ ∃ F, Relation.ReflTransGen (Step G) F₀ F ∧ Uncov G F a b :=
  Iff.rfl
end NashWilliams
