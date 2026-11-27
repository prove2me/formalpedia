-- Prove2me | solution 1 for MatchingPolytope.Multi.filter_collapse_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:22:03.270871+00:00
-- url     : https://prove2.me/submissions/cbf21221-d636-4f8a-b977-a88bdbb82e0d

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
theorem _root_.solution {R : Finset V} {r : V} (hr : r ∈ R) (hRW : R ⊆ W) :
    W.filter (fun u => collapse R r u ∈ ({r} : Finset V)) = R := by
  ext u
  rw [Finset.mem_filter]
  simp only [Finset.mem_singleton, collapse]
  constructor
  · rintro ⟨-, h⟩
    split_ifs at h with hu
    · exact hu
    · exact h ▸ hr
  · intro hu
    exact ⟨hRW hu, by simp [hu]⟩
end MatchingPolytope.Multi
