-- Prove2me | solution 1 for GwExact.cert_ok
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:24:17.42811+00:00
-- url     : https://prove2.me/submissions/c4d572e1-8698-4e10-b562-09a066bf53a4

module
public import Definitions.Def_GwExact_Rank
public import Definitions.Def_GwExact_Cert
public import Definitions.Def_GwExact_Upper

set_option autoImplicit true
@[expose] public section
public section
open GwExact
namespace GwExact
theorem _root_.solution : checkGw 53 5 4 cert = true := by decide +kernel
end GwExact
