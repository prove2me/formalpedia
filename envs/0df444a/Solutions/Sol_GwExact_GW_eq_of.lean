-- Prove2me | solution 1 for GwExact.GW_eq_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:24:28.564444+00:00
-- url     : https://prove2.me/submissions/7c87407f-4291-42c3-8c33-c10b6e0723a7

module
public import Definitions.Def_GwExact_Defs
public import Definitions.Def_GwExact_Clauses
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Fin
public import Definitions.Def_GwExact_Rank
public import Theorems.Thm_GwExact_lt_of_good

set_option autoImplicit true
@[expose] public section
public section
open GwExact
namespace GwExact
theorem _root_.solution {r l n : ℕ} {c : ℕ → Fin r} (hgood : IsGoodExactColouring r l n c)
    (hup : GWProperty r l (n + 1)) : GW r l = n + 1 :=
  le_antisymm (Nat.sInf_le hup) (le_csInf ⟨n + 1, hup⟩ fun _ hm => lt_of_good hgood hm)
end GwExact
