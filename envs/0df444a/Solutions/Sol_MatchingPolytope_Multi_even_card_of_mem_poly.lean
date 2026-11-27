-- Prove2me | solution 1 for MatchingPolytope.Multi.even_card_of_mem_poly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:23:17.455196+00:00
-- url     : https://prove2.me/submissions/a9aac56c-f4aa-4dd7-a11f-fab118bd05da

module
public import Mathlib
public import Definitions.Def_MatchingPolytope_Multigraph
public import Theorems.Thm_MatchingPolytope_Multi_gcut_self

set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}
variable {ends : E → Sym2 V} {W : Finset V} {F : Finset E}
namespace MatchingPolytope.Multi
theorem _root_.solution (hV : Valid ends W F) {x : E → ℝ} (hx : x ∈ Poly ends W F) :
    Even W.card := by
  by_contra h
  have := hx.2.2.2 W subset_rfl (Nat.not_even_iff_odd.1 h)
  rw [gcut_self hV subset_rfl] at this
  simp at this
  linarith
end MatchingPolytope.Multi
