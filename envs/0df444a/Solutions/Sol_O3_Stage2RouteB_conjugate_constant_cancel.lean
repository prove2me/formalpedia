-- Prove2me | solution 1 for O3.Stage2RouteB.conjugate_constant_cancel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:22:37.77041+00:00
-- url     : https://prove2.me/submissions/e524cd1b-e646-4f6a-bb0d-19541f6893de

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_Stage2RouteB
import Theorems.Thm_O3_Stage2RouteB_conjugateExponent_sub_one

set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteB
namespace O3.Stage2RouteB
theorem _root_.solution {p : ℝ} (hp : 1 < p) :
    (conjugateExponent p - 1) * (p - 1) = 1 := by
  have hne : p - 1 ≠ 0 := by linarith
  rw [conjugateExponent_sub_one hp]
  field_simp [hne]
end O3.Stage2RouteB
