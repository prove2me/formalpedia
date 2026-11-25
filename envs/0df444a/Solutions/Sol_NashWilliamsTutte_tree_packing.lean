-- Prove2me | solution 1 for NashWilliamsTutte.tree_packing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:35:31.112353+00:00
-- url     : https://prove2.me/submissions/3a81f7cd-9b2a-423a-83ce-60c1179e0c57

module
public import Mathlib
public import Definitions.Def_TreePackingLib_NashWilliams
public import Definitions.Def_NashWilliamsTrees_Solution
public import Theorems.Thm_NashWilliams_tree_packing


set_option autoImplicit true
@[expose] public section
public section
open Finset Fintype SimpleGraph
open NashWilliamsTutte
namespace NashWilliamsTutte
theorem _root_.solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V)
    (k : ℕ) :
    (∃ T : Fin k → SimpleGraph V, (∀ i, T i ≤ G ∧ (T i).IsTree) ∧
        Pairwise fun i j ↦ Disjoint (T i) (T j)) ↔
      ∀ f : V → V,
        k * (#(univ.image f) - 1) ≤ (G ⊓ (⊤ : SimpleGraph V).comap f).edgeSet.ncard :=
  NashWilliams.tree_packing G k
end NashWilliamsTutte
