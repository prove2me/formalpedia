-- Prove2me | solution 1 for MooreGraphs.card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:26:52.357929+00:00
-- url     : https://prove2.me/submissions/a3885d18-9e39-42cf-9a3b-70aa2502ec30

module
public import Mathlib
public import Definitions.Def_MooreLib_MooreGraphsAux
public import Definitions.Def_MooreLib_MooreGraphs
public import Theorems.Thm_MooreGraphs_ball2_eq_univ
public import Theorems.Thm_MooreGraphs_card_ball2_le


set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open MooreGraphs
variable {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
  [DecidableRel G.Adj]
namespace MooreGraphs
theorem _root_.solution {k : ℕ} (hreg : G.IsRegularOfDegree k) (hdiam : G.ediam ≤ 2) :
    Fintype.card V ≤ k ^ 2 + 1 := by
  classical
  obtain ⟨v⟩ := ‹Nonempty V›
  rw [← card_univ, ← ball2_eq_univ G hdiam v]
  exact card_ball2_le G hreg v
end MooreGraphs
