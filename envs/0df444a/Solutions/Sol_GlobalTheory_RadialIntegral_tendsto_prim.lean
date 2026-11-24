-- Prove2me | solution 1 for GlobalTheory.RadialIntegral.tendsto_prim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:47:43.235802+00:00
-- url     : https://prove2.me/submissions/ba3c6d97-6672-4ba2-ad68-109e68f9f26c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralComplexInvPowAddNormSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open GlobalTheory GlobalTheory.RadialIntegral
namespace GlobalTheory.RadialIntegral
theorem _root_.solution (m : ℕ) (a : ℝ) :
    Tendsto (fun r : ℝ => -(((a + r ^ 2) ^ (m + 1))⁻¹ / (2 * (m + 1)))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun r : ℝ => a + r ^ 2) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop two_ne_zero)
  have h2 : Tendsto (fun r : ℝ => (a + r ^ 2) ^ (m + 1)) atTop atTop :=
    (tendsto_pow_atTop (Nat.succ_ne_zero m)).comp h1
  simpa using ((h2.inv_tendsto_atTop).div_const (2 * ((m : ℝ) + 1))).neg
end GlobalTheory.RadialIntegral
