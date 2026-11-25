-- Prove2me | solution 1 for MooreGraphs.card_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:27:04.055636+00:00
-- url     : https://prove2.me/submissions/33762066-484c-43a6-8ea8-e772a873decd

module
public import Mathlib
public import Definitions.Def_MooreLib_MooreGraphsAux
public import Definitions.Def_MooreLib_MooreGraphs
public import Theorems.Thm_MooreGraphs_ball2_eq_univ
public import Theorems.Thm_MooreGraphs_card_ball2_eq


set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open MooreGraphs
variable {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
  [DecidableRel G.Adj]
namespace MooreGraphs
theorem _root_.solution {k : ℕ} (hreg : G.IsRegularOfDegree k) (hdiam : G.ediam ≤ 2)
    (hgirth : 5 ≤ G.egirth) : Fintype.card V = k ^ 2 + 1 := by
  classical
  obtain ⟨v⟩ := ‹Nonempty V›
  rw [← card_univ, ← ball2_eq_univ G hdiam v]
  exact card_ball2_eq G hreg hgirth v
end MooreGraphs
