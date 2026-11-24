-- Prove2me | solution 1 for GlobalTheory.ExponentialIntegralUnits.hasDerivAt_primitive
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:10.418833+00:00
-- url     : https://prove2.me/submissions/1f837d5a-c6f2-4b42-8711-6f21a82edf56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsUnitIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NormedSpace Filter Topology
open GlobalTheory GlobalTheory.ExponentialIntegralUnits
universe u_1
variable {𝔸 : Type u_1} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
namespace GlobalTheory.ExponentialIntegralUnits
theorem _root_.solution (M : ℝ → 𝔸) (hc : Continuous M) (t : ℝ) :
    HasDerivAt (fun u : ℝ => ∫ s in (0 : ℝ)..u, M s) (M t) t := by
  exact (hc.integral_hasStrictDerivAt 0 t).hasDerivAt
end GlobalTheory.ExponentialIntegralUnits
