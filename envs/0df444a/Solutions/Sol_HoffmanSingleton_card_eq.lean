-- Prove2me | solution 1 for HoffmanSingleton.card_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:37:43.599514+00:00
-- url     : https://prove2.me/submissions/c9198185-0358-4d3f-bcc4-cd367e5ed48a

module
public import Mathlib
public import Definitions.Def_MooreLib_MooreGraphs
public import Definitions.Def_MooreGraphsHoffmanSingleton_Solution
public import Theorems.Thm_MooreGraphs_card_eq


set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open HoffmanSingleton
variable {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
  [DecidableRel G.Adj]
namespace HoffmanSingleton
theorem _root_.solution {k : ℕ} (hreg : G.IsRegularOfDegree k) (hdiam : G.ediam ≤ 2)
    (hgirth : 5 ≤ G.egirth) : Fintype.card V = k ^ 2 + 1 :=
  MooreGraphs.card_eq G hreg hdiam hgirth
end HoffmanSingleton
