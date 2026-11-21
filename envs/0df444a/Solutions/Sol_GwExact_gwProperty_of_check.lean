-- Prove2me | solution 1 for GwExact.gwProperty_of_check
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:25:41.756756+00:00
-- url     : https://prove2.me/submissions/15bbb919-260e-48ee-8a38-89db313ae3a2

module
public import Definitions.Def_GwExact_Defs
public import Definitions.Def_GwExact_Clauses
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Fin
public import Definitions.Def_GwExact_Rank
public import Theorems.Thm_GwExact_goodPos_of_colouring
public import Theorems.Thm_GwExact_checkGw_sound


set_option autoImplicit true
@[expose] public section
public section
open GwExact
namespace GwExact
theorem _root_.solution {r R l n : ℕ} (hrR : r ≤ R) {steps : List Nat}
    (h : checkGw n R l steps = true) : GWProperty r l n := by
  intro m hm c hc
  obtain ⟨_, hrb, hmono⟩ := hc
  exact checkGw_sound steps h (goodPos_of_colouring (n := n) (l := l) hrR c
    (fun x d hx hd _ => hrb x d hx hd (by omega)) (fun x d hx hd _ => hmono x d hx hd (by omega)))
end GwExact
