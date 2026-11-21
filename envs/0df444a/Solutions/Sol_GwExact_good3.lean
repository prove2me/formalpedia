-- Prove2me | solution 1 for GwExact.good3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:19:55.285164+00:00
-- url     : https://prove2.me/submissions/bc3c0f4f-80c6-443b-8d38-f4f471190d98

module
public import Definitions.Def_GwExact_Defs
public import Definitions.Def_GwExact_Lower
public import Theorems.Thm_GwExact_isGood_of_goodB

set_option autoImplicit true
@[expose] public section
public section
open GwExact
namespace GwExact
theorem _root_.solution : IsGoodExactColouring 3 4 52 col3 := isGood_of_goodB (by decide) (by decide +kernel)
end GwExact
