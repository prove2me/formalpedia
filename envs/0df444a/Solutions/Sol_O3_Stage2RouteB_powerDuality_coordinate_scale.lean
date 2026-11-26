-- Prove2me | solution 1 for O3.Stage2RouteB.powerDuality_coordinate_scale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:22:07.219255+00:00
-- url     : https://prove2.me/submissions/c5e0e9ef-82b2-49a2-a16a-3c3dcb44341f

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_Stage2RouteB

set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteB
namespace O3.Stage2RouteB
theorem _root_.solution {q c b : ℝ} (hc : 0 < c) :
    |c * b| ^ (q - 2) * (c * b) =
      c ^ (q - 1) * (|b| ^ (q - 2) * b) := by
  rw [abs_mul, abs_of_pos hc]
  rw [Real.mul_rpow hc.le (abs_nonneg b)]
  rw [show c ^ (q - 2) * |b| ^ (q - 2) * (c * b) =
      (c ^ (q - 2) * c) * (|b| ^ (q - 2) * b) by ring]
  rw [show c ^ (q - 2) * c = c ^ (q - 1) by
    calc
      c ^ (q - 2) * c = c ^ (q - 2) * c ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = c ^ ((q - 2) + 1) := (Real.rpow_add hc _ _).symm
      _ = c ^ (q - 1) := by
        congr 1
        ring]
end O3.Stage2RouteB
