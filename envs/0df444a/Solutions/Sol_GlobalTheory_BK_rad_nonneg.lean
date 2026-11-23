-- Prove2me | solution 1 for GlobalTheory.BK.rad_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:19:12.207935+00:00
-- url     : https://prove2.me/submissions/59af734a-0aeb-4bc8-b0ae-ea9a171aa687

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
variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K]
namespace GlobalTheory.BK
theorem _root_.solution (l : ℕ) (k : ℝ) : 0 ≤ rad l k := Real.rpow_nonneg (Nat.cast_nonneg l) _
end GlobalTheory.BK
