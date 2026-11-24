-- Prove2me | solution 1 for GlobalTheory.BK.wS_anti
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:00:15.874816+00:00
-- url     : https://prove2.me/submissions/010cac06-8231-4d5b-a81f-8a6e0d939356

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
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace GlobalTheory.BK
theorem _root_.solution (e : ℕ) {i j : ℕ} (h : i ≤ j) : wS K e j ≤ wS K e i :=
  norm_natCast_le_of_dvd (Nat.factorial_dvd_factorial (Nat.div_le_div_right h))
end GlobalTheory.BK
