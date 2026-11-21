-- Prove2me | solution 1 for GwExact.exists_good_3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:24:49.653079+00:00
-- url     : https://prove2.me/submissions/78a0f366-8a64-4085-a9f3-bafb0a72c3dc

module
public import Definitions.Def_GwExact
public import Definitions.Def_GwExactSolution
public import Theorems.Thm_GwExact_good3


set_option autoImplicit true
@[expose] public section
public section
open GwExact
namespace GwExact
theorem _root_.solution : ∃ c : ℕ → Fin 3, IsGoodExactColouring 3 4 52 c := ⟨col3, good3⟩
end GwExact
