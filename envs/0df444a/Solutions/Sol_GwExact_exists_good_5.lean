-- Prove2me | solution 1 for GwExact.exists_good_5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:25:04.257717+00:00
-- url     : https://prove2.me/submissions/4be598ea-7b35-4a48-867c-f9ac44cd8883

module
public import Definitions.Def_GwExact
public import Definitions.Def_GwExactSolution
public import Theorems.Thm_GwExact_good5


set_option autoImplicit true
@[expose] public section
public section
open GwExact
namespace GwExact
theorem _root_.solution : ∃ c : ℕ → Fin 5, IsGoodExactColouring 5 4 52 c := ⟨col5, good5⟩
end GwExact
