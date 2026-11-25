-- Prove2me | solution 1 for HoffmanSingleton.hoffman_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:48:53.984073+00:00
-- url     : https://prove2.me/submissions/4390a255-66f1-42e3-8333-210e2e8a7c9e

module
public import Mathlib
public import Definitions.Def_MooreLib_MooreGraphs
public import Definitions.Def_MooreGraphsHoffmanSingleton_Solution
public import Theorems.Thm_MooreGraphs_hoffman_singleton


set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open HoffmanSingleton
variable {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
  [DecidableRel G.Adj]
namespace HoffmanSingleton
theorem _root_.solution {k : ℕ} (hk : 2 ≤ k) (hreg : G.IsRegularOfDegree k)
    (hdiam : G.ediam ≤ 2) (hgirth : 5 ≤ G.egirth) : k = 2 ∨ k = 3 ∨ k = 7 ∨ k = 57 :=
  MooreGraphs.hoffman_singleton G hk hreg hdiam hgirth
end HoffmanSingleton
