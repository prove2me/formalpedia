-- Prove2me | solution 1 for Mader.dbl_induce
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:53:05.046393+00:00
-- url     : https://prove2.me/submissions/f981776c-6cb5-4fc0-9c4a-5ed999054348

module
public import Mathlib
public import Definitions.Def_MaderLib_MaderAux
public import Theorems.Thm_Mader_dbl_eq_sum
public import Theorems.Thm_Mader_two_mul_ncard_edgeSet

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open Mader
variable {V : Type*}
variable (G : SimpleGraph V)
open Classical
namespace Mader
theorem _root_.solution (S : Finset V) :
    dbl G S = 2 * (G.induce (S : Set V)).edgeSet.ncard := by
  classical
  rw [two_mul_ncard_edgeSet, dbl_eq_sum, ← Finset.sum_finset_coe]
  refine sum_congr rfl (fun ⟨v, hv⟩ _ => ?_)
  unfold ndeg
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
  refine Finset.card_bij (fun w hw => ⟨w, (mem_filter.1 hw).1⟩) ?_ ?_ ?_
  · intro w hw
    simp only [mem_filter, mem_univ, true_and, comap_adj, Function.Embedding.coe_subtype]
    exact (mem_filter.1 hw).2
  · intro a _ b _ h
    simpa using h
  · rintro ⟨w, hw⟩ h
    simp only [mem_filter, mem_univ, true_and, comap_adj, Function.Embedding.coe_subtype] at h
    exact ⟨w, mem_filter.2 ⟨hw, h⟩, rfl⟩
end Mader
