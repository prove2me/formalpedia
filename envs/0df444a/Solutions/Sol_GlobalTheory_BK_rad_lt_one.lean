-- Prove2me | solution 1 for GlobalTheory.BK.rad_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:00:14.949818+00:00
-- url     : https://prove2.me/submissions/18f389cd-936c-4e9d-8c4a-1bcc3b0028af

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
variable {O K}
namespace GlobalTheory.BK
theorem _root_.solution (l : ℕ) [Fact l.Prime] {k : ℝ} (hk : 0 < k) : rad l k < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (Fact.out : l.Prime).one_lt) (by linarith)
end GlobalTheory.BK
