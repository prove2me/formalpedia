-- Prove2me | solution 1 for GlobalTheory.Hk.RayCont.norm_integrand_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:49.658806+00:00
-- url     : https://prove2.me/submissions/54fd3a36-def1-406f-a2fa-25fb68813b4d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyContinuationGrowth

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
theorem _root_.solution (hC : ∀ x, 1 ≤ x → ‖E x‖ ≤ C * Real.sqrt x) (s : ℂ) :
    ∀ᵐ t ∂(volume.restrict (Set.Ioi (1 : ℝ))),
      ‖E t * (t : ℂ) ^ (-s - 1)‖ ≤ C * t ^ (-(s.re + 1 / 2)) := by
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
  have ht0 : 0 < t := zero_lt_one.trans ht
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht0]
  refine (mul_le_mul_of_nonneg_right (hC _ (le_of_lt ht)) (Real.rpow_nonneg ht0.le _)).trans
    (le_of_eq ?_)
  rw [Real.sqrt_eq_rpow, mul_assoc, ← Real.rpow_add ht0]
  congr 2
  simp only [sub_re, neg_re, one_re]
  ring
end GlobalTheory.Hk.RayCont
