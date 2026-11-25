-- Prove2me | solution 1 for NashWilliamsTutte.arboricity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:32:53.206393+00:00
-- url     : https://prove2.me/submissions/2815132c-5cd0-4180-8f33-0012854057f7

module
public import Mathlib
public import Definitions.Def_TreePackingLib_NashWilliams
public import Definitions.Def_NashWilliamsTrees_Solution
public import Theorems.Thm_NashWilliams_arboricity


set_option autoImplicit true
@[expose] public section
public section
open Finset Fintype SimpleGraph
open NashWilliamsTutte
namespace NashWilliamsTutte
theorem _root_.solution {V : Type*} [Finite V] (G : SimpleGraph V) (k : ℕ) :
    (∃ F : Fin k → SimpleGraph V, (∀ i, F i ≤ G ∧ (F i).IsAcyclic) ∧ G = ⨆ i, F i) ↔
      ∀ S : Finset V, S.Nonempty → (G.induce (S : Set V)).edgeSet.ncard ≤ k * (#S - 1) :=
  NashWilliams.arboricity G k
end NashWilliamsTutte
