-- Prove2me | solution 1 for GwExact.good4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:22:24.765899+00:00
-- url     : https://prove2.me/submissions/e17954c6-935b-41de-b5cb-12c6b1867bc2

module
public import Definitions.Def_GwExact_Defs
public import Definitions.Def_GwExact_Lower
public import Theorems.Thm_GwExact_isGood_of_goodB

set_option autoImplicit true
@[expose] public section
public section
open GwExact
namespace GwExact
theorem _root_.solution : IsGoodExactColouring 4 4 52 col4 := isGood_of_goodB (by decide) (by decide +kernel)
end GwExact
