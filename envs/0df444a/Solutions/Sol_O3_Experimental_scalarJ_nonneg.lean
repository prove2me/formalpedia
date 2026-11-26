-- Prove2me | solution 1 for O3.Experimental.scalarJ_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:54:29.177621+00:00
-- url     : https://prove2.me/submissions/5319dd1e-4b67-471b-bf8e-0fddefd62e63

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_GeometryExperimental

set_option autoImplicit true
open O3 O3.Experimental
namespace O3.Experimental
theorem _root_.solution {p u : ℝ} (hp : 2 < p) (hu : 0 ≤ u) :
    scalarJ p u = u ^ (p - 1) := by
  rw [scalarJ, abs_of_nonneg hu]
  rw [← Real.rpow_add_one' hu (by linarith : p - 2 + 1 ≠ 0)]
  congr 1
  ring
end O3.Experimental
