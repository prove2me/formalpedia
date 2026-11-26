-- Prove2me | solution 1 for O3.Experimental.scalarJ_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:54:37.960225+00:00
-- url     : https://prove2.me/submissions/0e149fe8-94ca-454b-b160-c0f828c1619b

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_GeometryExperimental

set_option autoImplicit true
open O3 O3.Experimental
namespace O3.Experimental
theorem _root_.solution {p u : ℝ} (hp : 2 < p) (hu : u ≤ 0) :
    scalarJ p u = -((-u) ^ (p - 1)) := by
  rw [scalarJ, abs_of_nonpos hu]
  have hnu : 0 ≤ -u := neg_nonneg.mpr hu
  calc
    (-u) ^ (p - 2) * u = -((-u) ^ (p - 2) * (-u)) := by ring
    _ = -((-u) ^ (p - 1)) := by
      rw [← Real.rpow_add_one' hnu (by linarith : p - 2 + 1 ≠ 0)]
      congr 2
      ring
end O3.Experimental
