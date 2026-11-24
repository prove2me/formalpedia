-- Prove2me | solution 1 for GlobalTheory.ZetaHalfPlane.norm_fractInt_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:31:53.898254+00:00
-- url     : https://prove2.me/submissions/20ff7efa-9cbf-491c-bd31-fba9debff2b7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ZetaEqSubIntegralFract
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableAtFractInt
import Theorems.Thm_GlobalTheory_ZetaHalfPlane_norm_integrand_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open Set Filter Topology
open GlobalTheory GlobalTheory.ZetaHalfPlane
namespace GlobalTheory.ZetaHalfPlane
theorem _root_.solution {s : ℂ} (hs : 0 < s.re) : ‖fractInt s‖ ≤ 1 / s.re := by
  have h : -(s.re + 1) < -1 := by linarith
  calc ‖fractInt s‖ ≤ ∫ t in Ioi (1 : ℝ), t ^ (-(s.re + 1)) := by
        refine norm_integral_le_of_norm_le (integrableOn_Ioi_rpow_of_lt h one_pos) ?_
        rw [ae_restrict_iff' measurableSet_Ioi]
        exact Eventually.of_forall fun t ht => norm_integrand_le s ht
    _ = 1 / s.re := by
        rw [integral_Ioi_rpow_of_lt h one_pos, Real.one_rpow,
          show -(s.re + 1) + 1 = -s.re by ring, neg_div_neg_eq]
end GlobalTheory.ZetaHalfPlane
