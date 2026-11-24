-- Prove2me | solution 1 for GlobalTheory.BK.frob_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:00:12.772451+00:00
-- url     : https://prove2.me/submissions/e92569f6-28ae-43a5-b2c1-033a7f8c96a4

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
omit [IsUltrametricDist K] [IsUnitBall O K]
namespace GlobalTheory.BK
theorem _root_.solution (l : ℕ) [Fact l.Prime] : Function.Injective (frob K l) := fun f g h => by
  ext n
  have := congrArg (coeff (l * n)) h
  simpa [frob] using this
end GlobalTheory.BK
