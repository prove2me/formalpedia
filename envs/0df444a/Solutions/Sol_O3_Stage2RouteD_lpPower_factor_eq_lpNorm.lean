-- Prove2me | solution 1 for O3.Stage2RouteD.lpPower_factor_eq_lpNorm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:12:40.482801+00:00
-- url     : https://prove2.me/submissions/716f9158-d091-4756-802c-77f5741c33db

import Definitions.Def_O3_GeometryExperimental
import Definitions.Def_O3_Stage2RouteD
import Theorems.Thm_O3_lpPower_pos_of_ne_zero


set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteD
namespace O3.Stage2RouteD
theorem _root_.solution {q : ℝ} (hq : 0 < q) {d : ℕ}
    {z : Point d} (hz : z ≠ 0) :
    (lpPower q z) ^ (2 / q - 1) = (lpNorm q z) ^ (2 - q) := by
  have hS : 0 < lpPower q z := lpPower_pos_of_ne_zero hz
  unfold lpNorm
  rw [← Real.rpow_mul hS.le]
  congr 1
  field_simp
end O3.Stage2RouteD
