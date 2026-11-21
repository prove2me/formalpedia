-- Prove2me | solution 1 for GwExact.good5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:22:29.185582+00:00
-- url     : https://prove2.me/submissions/84d86acc-3633-43b8-bc25-54296ebb61da

module
public import Definitions.Def_GwExact_Defs
public import Definitions.Def_GwExact_Lower
public import Theorems.Thm_GwExact_isGood_of_goodB

set_option autoImplicit true
@[expose] public section
public section
open GwExact
namespace GwExact
theorem _root_.solution : IsGoodExactColouring 5 4 52 col5 := isGood_of_goodB (by decide) (by decide +kernel)
end GwExact
