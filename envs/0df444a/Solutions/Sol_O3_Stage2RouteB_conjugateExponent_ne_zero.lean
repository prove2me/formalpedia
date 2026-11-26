-- Prove2me | solution 1 for O3.Stage2RouteB.conjugateExponent_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:20:15.084037+00:00
-- url     : https://prove2.me/submissions/070d1e87-2535-44dd-bbd9-a3b9c49e806e

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_Stage2RouteB
import Theorems.Thm_O3_one_lt_conjugateExponent


set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteB
namespace O3.Stage2RouteB
theorem _root_.solution {p : ℝ} (hp : 1 < p) : conjugateExponent p ≠ 0 :=
  ne_of_gt (lt_trans zero_lt_one (one_lt_conjugateExponent hp))
end O3.Stage2RouteB
