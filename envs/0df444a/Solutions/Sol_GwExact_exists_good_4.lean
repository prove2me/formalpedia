-- Prove2me | solution 1 for GwExact.exists_good_4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:24:58.957309+00:00
-- url     : https://prove2.me/submissions/233a11c2-034d-48b0-96e0-f6acb2709eae

module
public import Definitions.Def_GwExact
public import Definitions.Def_GwExactSolution
public import Theorems.Thm_GwExact_good4


set_option autoImplicit true
@[expose] public section
public section
open GwExact
namespace GwExact
theorem _root_.solution : ∃ c : ℕ → Fin 4, IsGoodExactColouring 4 4 52 c := ⟨col4, good4⟩
end GwExact
