-- Prove2me | solution 1 for GwExact.GW_eq_53
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:27:21.910847+00:00
-- url     : https://prove2.me/submissions/23105709-d040-439f-b5b8-3a1d7bf5410c

module
public import Definitions.Def_GwExact
public import Definitions.Def_GwExactSolution
public import Theorems.Thm_GwExact_gwProperty_53
public import Theorems.Thm_GwExact_GW_eq_of
public import Theorems.Thm_GwExact_good3
public import Theorems.Thm_GwExact_good4
public import Theorems.Thm_GwExact_good5


set_option autoImplicit true
@[expose] public section
public section
open GwExact
namespace GwExact
theorem _root_.solution (r : ℕ) (h3 : 3 ≤ r) (h5 : r ≤ 5) : GW r 4 = 53 := by
  rcases (by omega : r = 3 ∨ r = 4 ∨ r = 5) with rfl | rfl | rfl
  · exact GW_eq_of good3 (gwProperty_53 3 (by decide))
  · exact GW_eq_of good4 (gwProperty_53 4 (by decide))
  · exact GW_eq_of good5 (gwProperty_53 5 (by decide))
end GwExact
