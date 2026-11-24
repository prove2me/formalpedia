-- Prove2me | solution 1 for GlobalTheory.Hk.RayCont.integrableOn_integrand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:32:25.797797+00:00
-- url     : https://prove2.me/submissions/ce6104a1-d134-48d7-a3f7-0c45ab8e961a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyContinuationGrowth
import Theorems.Thm_GlobalTheory_Hk_RayCont_norm_integrand_le

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
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.RayCont
open Asymptotics
variable {E : ℝ → ℂ} {C : ℝ}
namespace GlobalTheory.Hk.RayCont
theorem _root_.solution (hE : Measurable E)
    (hC : ∀ x, 1 ≤ x → ‖E x‖ ≤ C * Real.sqrt x) {s : ℂ} (hs : 1 / 2 < s.re) :
    IntegrableOn (fun t : ℝ => E t * (t : ℂ) ^ (-s - 1)) (Set.Ioi (1 : ℝ)) := by
  have hlt : -(s.re + 1 / 2) < -1 := by linarith
  refine Integrable.mono' ((integrableOn_Ioi_rpow_of_lt hlt zero_lt_one).const_mul C) ?_
    (norm_integrand_le hC s)
  exact (hE.mul (measurable_ofReal.pow_const _)).aestronglyMeasurable
end GlobalTheory.Hk.RayCont
