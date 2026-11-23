-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.isClique_arc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:40:33.502407+00:00
-- url     : https://prove2.me/submissions/bc9c38ad-e6b6-41df-9099-6a78b39cc5bc

import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_FractionGraphs
import Theorems.Thm_GroupTheoreticShannonCapacity_fractionGraph_adj_add_left
import Theorems.Thm_GroupTheoreticShannonCapacity_isClique_range_fractionGraph

set_option autoImplicit true
open GroupTheoreticShannonCapacity
open Matrix
namespace GroupTheoreticShannonCapacity
theorem _root_.solution (p q : ℕ) [NeZero p] (hq : 0 < q) (h2q : 2 * q ≤ p) (start : ZMod p) :
    (fractionGraph p q).IsClique ((Finset.range q).image (fun j : ℕ => start + j)) := by
  have hbase := isClique_range_fractionGraph p q hq h2q
  rw [SimpleGraph.isClique_iff] at hbase ⊢
  intro u hu v hv huv
  rw [Finset.mem_coe, Finset.mem_image] at hu hv
  obtain ⟨a, ha, rfl⟩ := hu
  obtain ⟨b, hb, rfl⟩ := hv
  rw [fractionGraph_adj_add_left]
  apply hbase
  · simp only [Finset.mem_coe, Finset.mem_image]; exact ⟨a, ha, rfl⟩
  · simp only [Finset.mem_coe, Finset.mem_image]; exact ⟨b, hb, rfl⟩
  · intro heq; apply huv; simpa using heq
end GroupTheoreticShannonCapacity
