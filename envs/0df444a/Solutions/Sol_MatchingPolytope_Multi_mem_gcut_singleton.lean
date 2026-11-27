-- Prove2me | solution 1 for MatchingPolytope.Multi.mem_gcut_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:22:01.46881+00:00
-- url     : https://prove2.me/submissions/d16a1f90-3d2e-4168-9e47-4eaa2c977e7b

module
public import Mathlib
public import Definitions.Def_MatchingPolytope_Multigraph
public import Theorems.Thm_MatchingPolytope_Multi_mem_gcut_singleton_of_nodiag

set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}
variable {ends : E → Sym2 V} {W : Finset V} {F : Finset E}
namespace MatchingPolytope.Multi
theorem _root_.solution (hV : Valid ends W F) {D : Finset E} (hD : D ⊆ F) {e : E} {v : V} :
    e ∈ gcut ends D {v} ↔ e ∈ D ∧ v ∈ ends e :=
  mem_gcut_singleton_of_nodiag fun e he => hV.nodiag e (hD he)
end MatchingPolytope.Multi
