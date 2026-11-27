-- Prove2me | solution 1 for MatchingPolytope.Multi.gw_swap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:28:06.669303+00:00
-- url     : https://prove2.me/submissions/50185727-492a-4efd-bc2e-f2b5a46ecf28

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
theorem _root_.solution (C : Finset E) (x : E → ℝ) (w1 w2 : Finset E → ℝ) (p : Finset E × Finset E) :
    gw C x w1 w2 p = gw C x w2 w1 p.swap := by
  unfold gw
  apply Finset.sum_congr rfl
  intro g _
  simp only [Prod.fst_swap, Prod.snd_swap]
  ring
end MatchingPolytope.Multi
