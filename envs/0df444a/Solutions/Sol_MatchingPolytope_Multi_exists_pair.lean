-- Prove2me | solution 1 for MatchingPolytope.Multi.exists_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:19:10.126811+00:00
-- url     : https://prove2.me/submissions/a2f1d194-2da2-4f0e-bdff-8810cfe8d26d

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
theorem _root_.solution (z : Sym2 V) : ∃ a b, z = s(a, b) := by
  induction z using Sym2.ind with
  | h a b => exact ⟨a, b, rfl⟩
end MatchingPolytope.Multi
