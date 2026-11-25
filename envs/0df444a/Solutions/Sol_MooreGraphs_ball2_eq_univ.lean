-- Prove2me | solution 1 for MooreGraphs.ball2_eq_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:19:59.107842+00:00
-- url     : https://prove2.me/submissions/6b904ba3-f7d6-4352-82ab-454c47516c9a

module
public import Mathlib
public import Definitions.Def_MooreLib_MooreGraphsAux
public import Theorems.Thm_MooreGraphs_exists_common_of_ediam

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph Matrix
open MooreGraphs
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
namespace MooreGraphs
theorem _root_.solution [DecidableEq V] (hdiam : G.ediam ≤ 2) (v : V) : ball2 G v = univ := by
  refine eq_univ_of_forall fun w => ?_
  simp only [ball2, mem_insert, mem_union, mem_neighborFinset, mem_biUnion, mem_erase]
  by_cases hwv : w = v
  · exact Or.inl hwv
  by_cases hadj : G.Adj v w
  · exact Or.inr (Or.inl hadj)
  obtain ⟨u, hvu, huw⟩ := exists_common_of_ediam G hdiam (Ne.symm hwv) hadj
  exact Or.inr (Or.inr ⟨u, hvu, hwv, huw⟩)
end MooreGraphs
