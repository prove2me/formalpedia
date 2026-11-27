-- Prove2me | solution 1 for MatchingPolytope.Multi.InHull.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:23:24.278562+00:00
-- url     : https://prove2.me/submissions/93ecfbd9-8ae4-4346-9f39-d8e16ec5d780

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
theorem _root_.solution {Q Q' : Finset E → Prop} (hQ : ∀ M, Q M → Q' M) {x : E → ℝ}
    (h : InHull Q x) : InHull Q' x := by
  obtain ⟨w, h0, h1, h2, h3⟩ := h
  exact ⟨w, h0, fun M hM => hQ M (h1 M hM), h2, h3⟩
end InHull
end MatchingPolytope.Multi
