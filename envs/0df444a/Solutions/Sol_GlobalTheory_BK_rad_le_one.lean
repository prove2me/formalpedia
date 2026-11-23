-- Prove2me | solution 1 for GlobalTheory.BK.rad_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:25:51.041386+00:00
-- url     : https://prove2.me/submissions/a54ed2d7-6d28-4ffb-830b-9dbcea2835bf

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
theorem _root_.solution (l : ℕ) [Fact l.Prime] {k : ℝ} (hk : 0 ≤ k) : rad l k ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (Fact.out : l.Prime).one_le) (by linarith)
end GlobalTheory.BK
