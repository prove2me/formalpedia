-- Prove2me | solution 1 for HamiltonDegree.chvatal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:38:01.852786+00:00
-- url     : https://prove2.me/submissions/f98a2655-4f1c-43b7-b79d-8114415e6706

module
public import Mathlib
public import Definitions.Def_ChvatalPosaLib_ChvatalPosa
public import Definitions.Def_ChvatalPosaHamiltonian_Solution
public import Theorems.Thm_ChvatalPosa_chvatal


set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open HamiltonDegree
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
namespace HamiltonDegree
theorem _root_.solution (hn : 3 ≤ Fintype.card V)
    (h : ∀ i : ℕ, 1 ≤ i → 2 * i < Fintype.card V →
      i ≤ #{v | G.degree v ≤ i} → i + 1 ≤ #{v | Fintype.card V - i ≤ G.degree v}) :
    G.IsHamiltonian :=
  ChvatalPosa.chvatal G hn h
end HamiltonDegree
