-- Prove2me | solution 1 for O3.Stage2RouteB.two_le_conjugateExponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:28:10.897224+00:00
-- url     : https://prove2.me/submissions/5a3a321d-57e9-44aa-b0c5-e450e78f58f5

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_Stage2RouteB
import Theorems.Thm_O3_conjugateExponent_eq


set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteB
namespace O3.Stage2RouteB
theorem _root_.solution {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) :
    2 ≤ conjugateExponent p := by
  rw [conjugateExponent_eq]
  rw [le_div_iff₀ (by linarith : 0 < p - 1)]
  linarith
end O3.Stage2RouteB
