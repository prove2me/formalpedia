-- Prove2me | solution 1 for NashWilliams.Uncov.adj_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:41:09.83662+00:00
-- url     : https://prove2.me/submissions/ef5d8a20-bd68-427e-bfb1-55429266c7ed

module
public import Mathlib
public import Definitions.Def_TreePackingLib_NashWilliamsAux

set_option autoImplicit true
@[expose] public section
public section
open Finset Fintype SimpleGraph Function
open NashWilliams
variable {V : Type*}
variable (G : SimpleGraph V) {k : ℕ}
variable {G}
namespace NashWilliams
namespace Uncov
theorem _root_.solution {F : Fin k → SimpleGraph V} {u v : V} (h : Uncov G F u v) {j : Fin k}
    {a b : V} (hab : s(a, b) = s(u, v)) : ¬ (F j).Adj a b := by
  rcases Sym2.eq_iff.1 hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h.2 j
  · exact fun h' ↦ h.2 j h'.symm
end Uncov
end NashWilliams
