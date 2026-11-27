-- Prove2me | solution 1 for MatchingPolytope.Multi.filter_collapse_other
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:21:59.383266+00:00
-- url     : https://prove2.me/submissions/c7ac2905-fcb6-479c-a150-ba6c9b336903

module
public import Definitions.Def_MatchingPolytope_Multigraph
public import Definitions.Def_MatchingPolytope_Shrink

set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}
variable [DecidableEq V]
variable {ends : E → Sym2 V} {W : Finset V} {F : Finset E}
namespace MatchingPolytope.Multi
theorem _root_.solution {R : Finset V} {r : V} (hr : r ∈ R) {v : V} (hv : v ∈ W)
    (hvR : v ∉ R) : W.filter (fun u => collapse R r u ∈ ({v} : Finset V)) = {v} := by
  ext u
  rw [Finset.mem_filter]
  simp only [Finset.mem_singleton, collapse]
  constructor
  · rintro ⟨-, h⟩
    split_ifs at h with hu
    · subst h; exact absurd hr hvR
    · exact h
  · rintro rfl
    exact ⟨hv, by simp [hvR]⟩
end MatchingPolytope.Multi
