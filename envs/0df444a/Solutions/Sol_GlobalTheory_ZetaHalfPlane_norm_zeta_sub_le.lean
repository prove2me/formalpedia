-- Prove2me | solution 1 for GlobalTheory.ZetaHalfPlane.norm_zeta_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:00:11.184677+00:00
-- url     : https://prove2.me/submissions/f1287e41-c26a-4fe1-ba15-6eea1083c9fd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ZetaEqSubIntegralFract
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableAtFractInt
import Theorems.Thm_GlobalTheory_ZetaHalfPlane_norm_fractInt_le
import Theorems.Thm_GlobalTheory_ZetaHalfPlane_zeta_eq

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
theorem _root_.solution :
    ∀ s : ℂ, 0 < s.re → s ≠ 1 → ‖riemannZeta s - s / (s - 1)‖ ≤ ‖s‖ / s.re := by
  intro s hs hs1
  rw [zeta_eq hs hs1, sub_sub_cancel_left, norm_neg, norm_mul, div_eq_mul_one_div]
  exact mul_le_mul_of_nonneg_left (norm_fractInt_le hs) (norm_nonneg s)
end GlobalTheory.ZetaHalfPlane
