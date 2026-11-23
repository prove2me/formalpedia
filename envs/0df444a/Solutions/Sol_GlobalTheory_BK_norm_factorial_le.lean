-- Prove2me | solution 1 for GlobalTheory.BK.norm_factorial_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:24:41.115984+00:00
-- url     : https://prove2.me/submissions/afd29607-a8cd-44e5-8dcb-1b907bd8970b

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
namespace GlobalTheory.BK
theorem _root_.solution (m : ℕ) : ‖(m.factorial : K)‖ ≤ ‖(l : K)‖ ^ (m / l) := by
  rw [← norm_pow, ← Nat.cast_pow]
  refine norm_natCast_le_of_dvd (Dvd.dvd.trans ?_
    (Nat.factorial_dvd_factorial (Nat.mul_div_le m l)))
  rw [padicValNat_dvd_iff_le (Nat.factorial_ne_zero _), padicValNat_factorial_mul]
  omega
end GlobalTheory.BK
