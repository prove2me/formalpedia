-- Prove2me | solution 1 for MatchingPolytope.Multi.Valid.pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:20:17.888639+00:00
-- url     : https://prove2.me/submissions/95ff6b3a-7d6b-476f-a0bc-5f3d5637a47f

module
public import Mathlib
public import Definitions.Def_MatchingPolytope_Multigraph
public import Theorems.Thm_MatchingPolytope_Multi_exists_pair

set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}
variable {ends : E → Sym2 V} {W : Finset V} {F : Finset E}
namespace MatchingPolytope.Multi
namespace Valid
theorem _root_.solution (hV : Valid ends W F) {e : E} (he : e ∈ F) :
    ∃ a b, a ≠ b ∧ a ∈ W ∧ b ∈ W ∧ ends e = s(a, b) := by
  obtain ⟨a, b, h⟩ := exists_pair (ends e)
  refine ⟨a, b, ?_, hV.sub e he a (by simp [h]), hV.sub e he b (by simp [h]), h⟩
  intro hab
  exact hV.nodiag e he (by simp [h, hab])
end Valid
end MatchingPolytope.Multi
