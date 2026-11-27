-- Prove2me | solution 1 for MatchingPolytope.Multi.mem_gcut_of_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:19:09.356858+00:00
-- url     : https://prove2.me/submissions/88629c96-54ef-47e3-8fc1-5790a70ba839

module
public import Mathlib
public import Definitions.Def_MatchingPolytope_Multigraph

set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}
namespace MatchingPolytope.Multi
theorem _root_.solution {ends : E → Sym2 V} {F : Finset E} {S : Finset V} {e : E} {a b : V}
    (h : ends e = s(a, b)) :
    e ∈ gcut ends F S ↔ e ∈ F ∧ (a ∈ S ∨ b ∈ S) ∧ (a ∉ S ∨ b ∉ S) := by
  simp [gcut, h]
end MatchingPolytope.Multi
