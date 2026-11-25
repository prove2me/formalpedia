-- Prove2me | solution 1 for NashWilliams.Step.valid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:51:28.057059+00:00
-- url     : https://prove2.me/submissions/59f2c276-2f31-4268-a33d-74173fce77e1

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
theorem _root_.solution {F F' : Fin k → SimpleGraph V} (hF : Valid G F) (h : Step G F F') :
    Valid G F' := by
  obtain ⟨i, u, v, x, y, huv, hxy, hac, rfl⟩ := h
  refine hF.update i (sup_le ((deleteEdges_le _).trans (hF.1 i).1)
    ((edge_le_iff _).2 (Or.inr huv.1))) hac fun a b hab ↦ ?_
  rcases adj_new hab with h | h
  · exact Or.inl h.1
  · exact Or.inr fun j ↦ huv.adj_iff h
end Step
end NashWilliams
