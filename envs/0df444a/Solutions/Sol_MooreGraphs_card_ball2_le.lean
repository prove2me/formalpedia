-- Prove2me | solution 1 for MooreGraphs.card_ball2_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:21:08.874605+00:00
-- url     : https://prove2.me/submissions/b133dd66-eb1c-429c-a30c-b4c491ffc662

module
public import Mathlib
public import Definitions.Def_MooreLib_MooreGraphsAux
public import Theorems.Thm_MooreGraphs_moore_count

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph Matrix
open MooreGraphs
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
namespace MooreGraphs
theorem _root_.solution [DecidableEq V] {k : ℕ} (hreg : G.IsRegularOfDegree k) (v : V) :
    (ball2 G v).card ≤ k ^ 2 + 1 := by
  rw [← moore_count]
  refine (card_insert_le _ _).trans ?_
  rw [add_comm 1]
  refine Nat.add_le_add_right ((card_union_le _ _).trans ?_) 1
  refine Nat.add_le_add ?_ ((card_biUnion_le).trans ?_)
  · rw [card_neighborFinset_eq_degree, hreg v]
  · refine le_of_eq ?_
    calc ∑ u ∈ G.neighborFinset v, ((G.neighborFinset u).erase v).card
        = ∑ u ∈ G.neighborFinset v, (k - 1) := by
          refine sum_congr rfl fun u hu => ?_
          rw [card_erase_of_mem (by simpa [mem_neighborFinset] using
            (G.mem_neighborFinset v u).1 hu |>.symm), card_neighborFinset_eq_degree, hreg u]
      _ = k * (k - 1) := by rw [sum_const, card_neighborFinset_eq_degree, hreg v, smul_eq_mul]
end MooreGraphs
