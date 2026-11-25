-- Prove2me | solution 1 for MooreGraphs.isSRGWith
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:32:34.495252+00:00
-- url     : https://prove2.me/submissions/58695b79-0097-4d7c-975b-c257c15da7db

module
public import Mathlib
public import Definitions.Def_MooreLib_MooreGraphsAux
public import Definitions.Def_MooreLib_MooreGraphs
public import Theorems.Thm_MooreGraphs_card_eq
public import Theorems.Thm_MooreGraphs_exists_common_of_ediam
public import Theorems.Thm_MooreGraphs_no_square
public import Theorems.Thm_MooreGraphs_no_triangle


set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open MooreGraphs
variable {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
  [DecidableRel G.Adj]
namespace MooreGraphs
theorem _root_.solution {k : ℕ} (hreg : G.IsRegularOfDegree k) (hdiam : G.ediam ≤ 2)
    (hgirth : 5 ≤ G.egirth) : G.IsSRGWith (k ^ 2 + 1) k 0 1 := by
  refine ⟨card_eq G hreg hdiam hgirth, hreg, fun v w h => ?_, fun v w hvw h => ?_⟩
  · rw [Fintype.card_eq_zero_iff]
    refine ⟨fun ⟨x, hx⟩ => ?_⟩
    rw [mem_commonNeighbors] at hx
    exact no_triangle G hgirth h hx.2 hx.1.symm
  · rw [Fintype.card_eq_one_iff]
    obtain ⟨x, hvx, hxw⟩ := exists_common_of_ediam G hdiam hvw h
    refine ⟨⟨x, (G.mem_commonNeighbors).2 ⟨hvx, hxw.symm⟩⟩, fun ⟨y, hy⟩ => ?_⟩
    rw [mem_commonNeighbors] at hy
    by_contra hne
    have hxy : y ≠ x := fun e => hne (Subtype.ext e)
    exact no_square G hgirth hvx hxw hy.2 hy.1.symm hvw hxy.symm
end MooreGraphs
