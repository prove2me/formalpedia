-- Prove2me | solution 1 for MatchingPolytope.Multi.InHull.exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:34:42.380215+00:00
-- url     : https://prove2.me/submissions/4b8fd110-0dea-427e-9949-a8d216c1891b

module
public import Mathlib
public import Definitions.Def_MatchingPolytope_Multigraph

set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}
variable {ends : E → Sym2 V} {W : Finset V} {F : Finset E}
variable [Fintype E]
namespace MatchingPolytope.Multi
namespace InHull
theorem _root_.solution {Q : Finset E → Prop} {x : E → ℝ} (h : InHull Q x) : ∃ M, Q M := by
  obtain ⟨w, -, h1, h2, -⟩ := h
  have : ∑ M, w M ≠ 0 := by rw [h2]; norm_num
  obtain ⟨M, -, hM⟩ := Finset.exists_ne_zero_of_sum_ne_zero this
  exact ⟨M, h1 M hM⟩
end InHull
end MatchingPolytope.Multi
