-- Prove2me | solution 1 for NashWilliams.Step.uncov
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:46:34.523946+00:00
-- url     : https://prove2.me/submissions/6ecb9ab2-4d0e-4d82-85d1-505dbc04e913

module
public import Mathlib
public import Definitions.Def_TreePackingLib_NashWilliamsAux
public import Theorems.Thm_NashWilliams_Uncov_adj_iff
public import Theorems.Thm_NashWilliams_adj_new

set_option autoImplicit true
@[expose] public section
public section
open Finset Fintype SimpleGraph Function
open NashWilliams
variable {V : Type*}
variable (G : SimpleGraph V) {k : ℕ}
variable {G}
namespace NashWilliams
namespace Step
theorem _root_.solution {F : Fin k → SimpleGraph V} (hF : Valid G F) {i : Fin k} {u v x y : V}
    (huv : Uncov G F u v) (hxy : (F i).Adj x y) :
    Uncov G (update F i ((F i).deleteEdges {s(x, y)} ⊔ edge u v)) x y := by
  refine ⟨(hF.1 i).1 hxy, fun j ↦ ?_⟩
  by_cases hj : j = i
  · subst hj
    simp only [update_self]
    intro h
    rcases adj_new h with h | h
    · exact h.2 rfl
    · exact huv.adj_iff h hxy
  · simp only [update_of_ne hj]
    exact disjoint_iff_adj.1 (hF.2 (Ne.symm hj)) x y hxy
end Step
end NashWilliams
