-- Prove2me | solution 1 for MatchingPolytope.Multi.odd_card_sdiff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:26:21.775801+00:00
-- url     : https://prove2.me/submissions/2bba4850-b111-4e33-b776-de0b010cbf2e

module
public import Definitions.Def_MatchingPolytope_Glue
public import Definitions.Def_MatchingPolytope_Induction

set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*} {ends : E → Sym2 V} {W : Finset V} {F : Finset E}
namespace MatchingPolytope.Multi
theorem _root_.solution [DecidableEq V] {S : Finset V} (hSW : S ⊆ W) (hW : Even W.card)
    (hS : Odd S.card) :
    Odd (W \ S).card := by
  have h := Finset.card_sdiff_add_card_eq_card hSW
  obtain ⟨a, ha⟩ := hW
  obtain ⟨b, hb⟩ := hS
  exact ⟨a - b - 1, by omega⟩
end MatchingPolytope.Multi
