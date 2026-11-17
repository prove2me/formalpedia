-- Prove2me | solution 1 for N25.siegelFun_reflect_first_index
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:47:51.160974+00:00
-- url     : https://prove2.me/submissions/2a6eb06c-1a83-47f6-9c5f-76051d955098

import Mathlib
import Definitions.Def_ModularCurve_SiegelFunction
import Theorems.Thm_ModularCurve_SiegelUnit_siegelFun_add_level
import Theorems.Thm_N25_siegelFun_neg_first_index

set_option autoImplicit false

namespace N25

/-- At second index zero, reflection across half the level preserves the
unpowered Siegel function on the upper half plane. -/
theorem _root_.solution (N : ℕ) (r : ℤ) (τ : UpperHalfPlane) :
    ModularCurve.siegelFun N ((N : ℤ)-r) 0 (τ : ℂ) =
      ModularCurve.siegelFun N r 0 (τ : ℂ) := by
  have h := (ModularCurve.SiegelUnit.siegelFun_add_level N (-r) 0).2 τ
  have h' : ModularCurve.siegelFun N (-r + N) 0 (τ : ℂ) =
      -ModularCurve.siegelFun N (-r) 0 (τ : ℂ) := by simpa using h
  rw [show (N : ℤ)-r = -r+N by ring, h', siegelFun_neg_first_index, neg_neg]

end N25
