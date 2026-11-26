-- Prove2me | solution 1 for O3.Experimental.hasDerivAt_scalarEnergy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:54:40.55838+00:00
-- url     : https://prove2.me/submissions/667fc80c-1cf3-40d2-94f5-4440cb4b8e91

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_GeometryExperimental

set_option autoImplicit true
open O3 O3.Experimental
namespace O3.Experimental
theorem _root_.solution {p : ℝ} (hp : 2 < p) (x : ℝ) :
    HasDerivAt (scalarEnergy p) (scalarJ p x) x := by
  have h := (hasDerivAt_abs_rpow x (by linarith : 1 < p)).div_const p
  have heq : scalarJ p x = p * |x| ^ (p - 2) * x / p := by
    unfold scalarJ
    field_simp
  rw [heq]
  exact h
end O3.Experimental
