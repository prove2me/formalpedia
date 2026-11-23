-- Prove2me | solution 1 for GlobalTheory.BK.rad_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:25:51.824979+00:00
-- url     : https://prove2.me/submissions/b539a10b-ce8a-431b-b62a-333a5ffd1f7a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NormPowLeNormFactorial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K]
include l
omit [IsUltrametricDist K]
namespace GlobalTheory.BK
theorem _root_.solution (e : ℕ) [NeZero e] : rad l (1 / e) ^ e = ‖(l : K)‖ := by
  have he : (e : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne e
  rw [norm_l, rad, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg l), neg_mul,
    one_div_mul_cancel he, Real.rpow_neg_one]
end GlobalTheory.BK
