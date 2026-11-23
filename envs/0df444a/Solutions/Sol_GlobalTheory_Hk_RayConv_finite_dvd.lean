-- Prove2me | solution 1 for GlobalTheory.Hk.RayConv.finite_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:49.873119+00:00
-- url     : https://prove2.me/submissions/3c8c2465-d13b-46b5-b9e7-8c8154a26cb7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FiniteIdealsIn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.RayConv
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.Hk.RayConv
theorem _root_.solution {I : Ideal (𝓞 K)} (hI : I ≠ 0) : {J : Ideal (𝓞 K) | J ∣ I}.Finite := by
  refine (Ideal.finite_setOf_absNorm_le (S := 𝓞 K) (Ideal.absNorm I)).subset fun J hJ => ?_
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero fun h => hI (Ideal.absNorm_eq_zero_iff.1 h)) (map_dvd _ hJ)
end GlobalTheory.Hk.RayConv
