-- Prove2me | solution 1 for O3.Stage2RouteB.mul_conjugateExponent_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:19:22.648261+00:00
-- url     : https://prove2.me/submissions/8c986147-1636-4d43-989c-58afa17b3511

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_Stage2RouteB
import Theorems.Thm_O3_conjugateExponent_eq


set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteB
namespace O3.Stage2RouteB
theorem _root_.solution {p : ℝ} (hp : 1 < p) :
    (p - 1) * conjugateExponent p = p := by
  have hne : p - 1 ≠ 0 := by linarith
  rw [conjugateExponent_eq]
  field_simp [hne]
end O3.Stage2RouteB
