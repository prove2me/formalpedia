-- Prove2me | solution 1 for MatchingPolytope.Multi.card_shrinkW_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:25:43.788101+00:00
-- url     : https://prove2.me/submissions/ff2166a9-ca7c-4250-9f71-1ca6df305058

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
theorem _root_.solution {R : Finset V} (hRW : R ⊆ W) (hR : 1 < R.card) (r : V) :
    (shrinkW W R r).card < W.card := by
  have h1 := Finset.card_insert_le r (W \ R)
  have h2 := Finset.card_sdiff_of_subset hRW
  have h3 := Finset.card_le_card hRW
  unfold shrinkW
  omega
end MatchingPolytope.Multi
