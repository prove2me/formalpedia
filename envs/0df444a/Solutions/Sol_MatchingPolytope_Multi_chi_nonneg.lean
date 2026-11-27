-- Prove2me | solution 1 for MatchingPolytope.Multi.chi_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:25:03.066207+00:00
-- url     : https://prove2.me/submissions/021e3b86-3732-4be8-a68a-51eac64f2c20

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
theorem _root_.solution (M : Finset E) (e : E) : 0 ≤ chi M e := by
  unfold chi; split_ifs <;> norm_num
end MatchingPolytope.Multi
