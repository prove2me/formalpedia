-- Prove2me | solution 1 for GwExact.gwProperty_53_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:26:15.507995+00:00
-- url     : https://prove2.me/submissions/a6d030ef-c00e-4b63-8107-24259246e78c

module
public import Definitions.Def_GwExact_Rank
public import Definitions.Def_GwExact_Cert
public import Definitions.Def_GwExact_Upper
public import Theorems.Thm_GwExact_cert_ok
public import Theorems.Thm_GwExact_gwProperty_of_check


set_option autoImplicit true
@[expose] public section
public section
open GwExact
namespace GwExact
theorem _root_.solution {r : ℕ} (hr : r ≤ 5) : GWProperty r 4 53 := gwProperty_of_check hr cert_ok
end GwExact
