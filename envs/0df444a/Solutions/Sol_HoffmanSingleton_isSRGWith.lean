-- Prove2me | solution 1 for HoffmanSingleton.isSRGWith
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:44:23.834544+00:00
-- url     : https://prove2.me/submissions/8447b7c2-c16e-45ad-a66a-600ac562fd83

module
public import Mathlib
public import Definitions.Def_MooreLib_MooreGraphs
public import Definitions.Def_MooreGraphsHoffmanSingleton_Solution
public import Theorems.Thm_MooreGraphs_isSRGWith


set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open HoffmanSingleton
variable {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
  [DecidableRel G.Adj]
namespace HoffmanSingleton
theorem _root_.solution {k : ℕ} (hreg : G.IsRegularOfDegree k) (hdiam : G.ediam ≤ 2)
    (hgirth : 5 ≤ G.egirth) : G.IsSRGWith (k ^ 2 + 1) k 0 1 :=
  MooreGraphs.isSRGWith G hreg hdiam hgirth
end HoffmanSingleton
