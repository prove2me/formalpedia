-- Prove2me | solution 1 for GwExact.gwProperty_53
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:26:48.716929+00:00
-- url     : https://prove2.me/submissions/df67566d-d4e3-4941-83d9-829e9ccd93fd

module
public import Definitions.Def_GwExact
public import Definitions.Def_GwExactSolution
public import Theorems.Thm_GwExact_gwProperty_53_of_le


set_option autoImplicit true
@[expose] public section
public section
open GwExact
namespace GwExact
theorem _root_.solution (r : ℕ) (hr : r ≤ 5) : GWProperty r 4 53 :=
  gwProperty_53_of_le hr
end GwExact
