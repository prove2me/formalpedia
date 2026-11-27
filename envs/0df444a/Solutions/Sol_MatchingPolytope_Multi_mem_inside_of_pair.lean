-- Prove2me | solution 1 for MatchingPolytope.Multi.mem_inside_of_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:19:12.052801+00:00
-- url     : https://prove2.me/submissions/f61c930b-6e10-410e-bd7f-00937321e425

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
    e ∈ inside ends F S ↔ e ∈ F ∧ a ∈ S ∧ b ∈ S := by
  simp [inside, h]
end MatchingPolytope.Multi
