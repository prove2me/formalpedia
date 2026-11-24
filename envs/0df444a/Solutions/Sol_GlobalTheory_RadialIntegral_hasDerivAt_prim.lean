-- Prove2me | solution 1 for GlobalTheory.RadialIntegral.hasDerivAt_prim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:47:37.635899+00:00
-- url     : https://prove2.me/submissions/bb68a2c5-a35a-4e6e-b1a6-006f3a7b974a

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
theorem _root_.solution (m : ℕ) (a : ℝ) (ha : 0 < a) (r : ℝ) :
    HasDerivAt (fun r : ℝ => -(((a + r ^ 2) ^ (m + 1))⁻¹ / (2 * (m + 1))))
      (r * ((a + r ^ 2) ^ (m + 2))⁻¹) r := by
  have hp : 0 < a + r ^ 2 := by positivity
  have h1 : HasDerivAt (fun r : ℝ => a + r ^ 2) (2 * r) r := by
    simpa using ((hasDerivAt_pow 2 r).const_add a)
  have h2 := ((((h1.pow (m + 1)).inv (pow_ne_zero _ hp.ne')).div_const (2 * ((m : ℝ) + 1))).neg)
  refine h2.congr_deriv ?_
  simp only [Pi.pow_apply, Nat.add_sub_cancel]
  have : (m : ℝ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp
  ring
end GlobalTheory.RadialIntegral
