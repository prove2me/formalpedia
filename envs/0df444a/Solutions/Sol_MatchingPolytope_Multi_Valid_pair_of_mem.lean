-- Prove2me | solution 1 for MatchingPolytope.Multi.Valid.pair_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:22:33.888215+00:00
-- url     : https://prove2.me/submissions/8bfa1ab8-d54c-4a60-a898-b88dfe5cc888

module
public import Mathlib
public import Definitions.Def_MatchingPolytope_Multigraph
public import Theorems.Thm_MatchingPolytope_Multi_Valid_pair

set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}
variable {ends : E → Sym2 V} {W : Finset V} {F : Finset E}
namespace MatchingPolytope.Multi
namespace Valid
theorem _root_.solution (hV : Valid ends W F) {e : E} (he : e ∈ F) {v : V} (hv : v ∈ ends e) :
    ∃ b, b ≠ v ∧ b ∈ W ∧ ends e = s(v, b) := by
  obtain ⟨a, b, hab, ha, hb, h⟩ := hV.pair he
  rw [h, Sym2.mem_iff] at hv
  rcases hv with rfl | rfl
  · exact ⟨b, hab.symm, hb, h⟩
  · exact ⟨a, hab, ha, h.trans Sym2.eq_swap⟩
end Valid
end MatchingPolytope.Multi
