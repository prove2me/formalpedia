-- Prove2me | solution 1 for HoffmanSingleton.card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:37:32.360414+00:00
-- url     : https://prove2.me/submissions/81ecd1c5-ea6e-4928-bc17-61214bb88315

module
public import Mathlib
public import Definitions.Def_MooreLib_MooreGraphs
public import Definitions.Def_MooreGraphsHoffmanSingleton_Solution
public import Theorems.Thm_MooreGraphs_card_le


set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open HoffmanSingleton
variable {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
  [DecidableRel G.Adj]
namespace HoffmanSingleton
theorem _root_.solution {k : ℕ} (hreg : G.IsRegularOfDegree k) (hdiam : G.ediam ≤ 2) :
    Fintype.card V ≤ k ^ 2 + 1 :=
  MooreGraphs.card_le G hreg hdiam
end HoffmanSingleton
