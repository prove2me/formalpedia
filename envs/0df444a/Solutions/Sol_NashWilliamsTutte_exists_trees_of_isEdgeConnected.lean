-- Prove2me | solution 1 for NashWilliamsTutte.exists_trees_of_isEdgeConnected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:35:48.374038+00:00
-- url     : https://prove2.me/submissions/a77bb2a3-f8c1-46cc-bf42-b4ef961cafe4

module
public import Mathlib
public import Definitions.Def_TreePackingLib_NashWilliams
public import Definitions.Def_NashWilliamsTrees_Solution
public import Theorems.Thm_NashWilliams_exists_trees_of_isEdgeConnected


set_option autoImplicit true
@[expose] public section
public section
open Finset Fintype SimpleGraph
open NashWilliamsTutte
namespace NashWilliamsTutte
theorem _root_.solution {V : Type*} [Finite V] [Nonempty V]
    (G : SimpleGraph V) (k : ℕ) (hG : G.IsEdgeConnected (2 * k)) :
    ∃ T : Fin k → SimpleGraph V, (∀ i, T i ≤ G ∧ (T i).IsTree) ∧
      Pairwise fun i j ↦ Disjoint (T i) (T j) :=
  NashWilliams.exists_trees_of_isEdgeConnected G k hG
end NashWilliamsTutte
