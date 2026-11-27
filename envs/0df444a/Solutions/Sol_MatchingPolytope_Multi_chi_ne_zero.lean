-- Prove2me | solution 1 for MatchingPolytope.Multi.chi_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:25:10.661127+00:00
-- url     : https://prove2.me/submissions/7be3b9b7-02b4-4d81-924e-dd5485755801

module
public import Definitions.Def_MatchingPolytope_Shrink
public import Definitions.Def_MatchingPolytope_Glue

set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}
namespace MatchingPolytope.Multi
theorem _root_.solution {M : Finset E} {e : E} (h : chi M e ≠ 0) : e ∈ M := by
  unfold chi at h; split_ifs at h with h'
  · exact h'
  · exact absurd rfl h
end MatchingPolytope.Multi
