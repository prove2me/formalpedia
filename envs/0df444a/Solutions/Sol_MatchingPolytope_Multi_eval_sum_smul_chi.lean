-- Prove2me | solution 1 for MatchingPolytope.Multi.eval_sum_smul_chi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:28:40.177556+00:00
-- url     : https://prove2.me/submissions/39f4b2f5-8692-4e2a-b5f4-4dec92a94325

module
public import Definitions.Def_MatchingPolytope_Shrink
public import Definitions.Def_MatchingPolytope_Glue

set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}
variable {ends : E → Sym2 V} {W : Finset V} {F : Finset E}
variable [DecidableEq V]
namespace MatchingPolytope.Multi
theorem _root_.solution [Fintype E] (w : Finset E → ℝ) (e : E) :
    (∑ M, w M • chi M) e = ∑ M, w M * chi M e := by
  simp [Finset.sum_apply]
end MatchingPolytope.Multi
