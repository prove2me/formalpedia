-- Prove2me | solution 1 for NashWilliams.nash_williams_simple
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:47:57.331949+00:00
-- url     : https://prove2.me/submissions/7834cc80-29ea-4e1a-9420-4256cf216f26

module
public import Mathlib
public import Definitions.Def_NashWilliamsLib_Orientation
public import Definitions.Def_NashWilliamsLib_Defs
public import Theorems.Thm_NashWilliams_nash_williams
public import Theorems.Thm_NashWilliams_adj_edgeEnds
public import Theorems.Thm_NashWilliams_two_mul_le_cut_edgeEnds
public import Theorems.Thm_NashWilliams_toDigraph_toSimpleGraphInclusive
public import Theorems.Thm_NashWilliams_toDigraph_antisymm
public import Theorems.Thm_NashWilliams_outCut_le_card

set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V : Type*} (G : SimpleGraph V)
open Classical
namespace NashWilliams
theorem _root_.solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (k : ℕ)
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsEdgeConnected (2 * k)) :
    ∃ D : Digraph V, D.toSimpleGraphInclusive = G ∧ (∀ u v, D.Adj u v → ¬ D.Adj v u) ∧
      ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ →
        k ≤ ((S ×ˢ Sᶜ).filter fun q => D.Adj q.1 q.2).card := by
  obtain ⟨o, ho⟩ := nash_williams k (edgeEnds G)
    (fun e => G.ne_of_adj (adj_edgeEnds G e))
    (fun S hne hneT => two_mul_le_cut_edgeEnds G hG hne hneT)
  exact ⟨toDigraph G o, toDigraph_toSimpleGraphInclusive G o, toDigraph_antisymm G o,
    fun S hne hneT => (ho S hne hneT).trans (outCut_le_card G o S)⟩
end NashWilliams
