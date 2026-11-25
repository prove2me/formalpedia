-- Prove2me | solution 1 for MooreGraphs.card_ball2_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:21:10.9968+00:00
-- url     : https://prove2.me/submissions/f7123f3f-f375-44ce-8c76-a7414421e626

module
public import Mathlib
public import Definitions.Def_MooreLib_MooreGraphsAux
public import Theorems.Thm_MooreGraphs_no_triangle
public import Theorems.Thm_MooreGraphs_no_square
public import Theorems.Thm_MooreGraphs_moore_count

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph Matrix
open MooreGraphs
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
namespace MooreGraphs
theorem _root_.solution [DecidableEq V] {k : ℕ} (hreg : G.IsRegularOfDegree k)
    (hgirth : 5 ≤ G.egirth) (v : V) : (ball2 G v).card = k ^ 2 + 1 := by
  rw [← moore_count, ball2, card_insert_of_notMem, add_comm 1, card_union_of_disjoint,
    card_biUnion]
  · rw [card_neighborFinset_eq_degree, hreg v]
    congr 2
    calc ∑ u ∈ G.neighborFinset v, ((G.neighborFinset u).erase v).card
        = ∑ u ∈ G.neighborFinset v, (k - 1) := by
          refine sum_congr rfl fun u hu => ?_
          rw [card_erase_of_mem (by simpa [mem_neighborFinset] using
            (G.mem_neighborFinset v u).1 hu |>.symm), card_neighborFinset_eq_degree, hreg u]
      _ = k * (k - 1) := by rw [sum_const, card_neighborFinset_eq_degree, hreg v, smul_eq_mul]
  · intro u hu u' hu' huu'
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro w hw hw'
    simp only [coe_neighborFinset, mem_neighborSet, mem_erase,
      mem_neighborFinset] at hu hu' hw hw'
    exact no_square G hgirth hu hw.2 hw'.2.symm hu'.symm hw.1.symm huu'
  · rw [Finset.disjoint_left]
    intro w hw hw'
    simp only [mem_biUnion, mem_erase, mem_neighborFinset] at hw hw'
    obtain ⟨u, hu, -, huw⟩ := hw'
    exact no_triangle G hgirth hu huw hw.symm
  · simp only [mem_union, mem_biUnion, mem_erase, mem_neighborFinset, not_or, not_exists,
      not_and]
    exact ⟨G.loopless.irrefl v, fun u _ h => (h rfl).elim⟩
end MooreGraphs
