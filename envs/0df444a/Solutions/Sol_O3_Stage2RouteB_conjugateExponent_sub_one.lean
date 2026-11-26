-- Prove2me | solution 1 for O3.Stage2RouteB.conjugateExponent_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:21:51.149789+00:00
-- url     : https://prove2.me/submissions/45457e18-bdb1-45cf-95c8-c936bbdd79cd

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_Stage2RouteB
import Theorems.Thm_O3_conjugateExponent_eq


set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteB
namespace O3.Stage2RouteB
theorem _root_.solution {p : ℝ} (hp : 1 < p) :
    conjugateExponent p - 1 = 1 / (p - 1) := by
  have hne : p - 1 ≠ 0 := by linarith
  rw [conjugateExponent_eq]
  field_simp [hne]
  ring
end O3.Stage2RouteB
