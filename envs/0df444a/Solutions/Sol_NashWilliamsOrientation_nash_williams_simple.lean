-- Prove2me | solution 1 for NashWilliamsOrientation.nash_williams_simple
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:50:47.773933+00:00
-- url     : https://prove2.me/submissions/e42c3931-1e59-4b50-ad87-08be0bfdfe10

module
public import Mathlib
public import Definitions.Def_NashWilliamsLib_Defs
public import Definitions.Def_NashWilliamsOrientation_Solution
public import Theorems.Thm_NashWilliams_nash_williams_simple


set_option autoImplicit true
@[expose] public section
public section
open NashWilliamsOrientation
open Classical
namespace NashWilliamsOrientation
theorem _root_.solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (k : ℕ)
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsEdgeConnected (2 * k)) :
    ∃ D : Digraph V, D.toSimpleGraphInclusive = G ∧ (∀ u v, D.Adj u v → ¬ D.Adj v u) ∧
      ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ →
        k ≤ ((S ×ˢ Sᶜ).filter fun q => D.Adj q.1 q.2).card :=
  NashWilliams.nash_williams_simple k G hG
end NashWilliamsOrientation
