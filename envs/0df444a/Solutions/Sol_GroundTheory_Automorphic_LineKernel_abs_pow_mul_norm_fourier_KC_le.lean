-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.abs_pow_mul_norm_fourier_KC_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:50:07.631707+00:00
-- url     : https://prove2.me/submissions/9693b1cc-218f-4a37-a5ce-1c2d2eac8b98

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineStage
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineBounds
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_fourier_KC_zero
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_fourier_KC_succ
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_norm_fourier_KC_le_one
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_abs_mul_norm_khat_le
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_norm_khat_le_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Set Filter Topology Real Function ContinuousLinearMap
open scoped ContDiff Convolution Pointwise FourierTransform
set_option linter.unusedSectionVars false
noncomputable section
open GroundTheory.Automorphic.LineKernel
variable {a r : ℕ → ℝ} (ha : ∀ j, 0 < a j) (hr : ∀ j, 0 < r j)
include ha hr
namespace GroundTheory.Automorphic.LineKernel
theorem _root_.solution (n m : ℕ) (hmn : m ≤ n + 1) (ξ : ℝ) :
    |ξ| ^ m * ‖𝓕 (KC a r n) ξ‖ ≤ ∏ j ∈ Finset.range m, (a j / π) := by
  induction n generalizing m with
  | zero =>
    interval_cases m
    · simpa using norm_fourier_KC_le_one ha hr 0 ξ
    · simpa [fourier_KC_zero ha hr] using abs_mul_norm_khat_le (ha 0) (hr 0) ξ
  | succ n ih =>
    rw [fourier_KC_succ ha hr, norm_mul]
    rcases Nat.lt_or_ge m (n + 2) with h | h
    · calc |ξ| ^ m * (‖𝓕 (KC a r n) ξ‖ * ‖khat (a (n + 1)) (r (n + 1)) ξ‖)
          ≤ |ξ| ^ m * (‖𝓕 (KC a r n) ξ‖ * 1) := by
            gcongr; exact norm_khat_le_one (ha _) (hr _) ξ
        _ ≤ _ := by rw [mul_one]; exact ih m (by omega)
    · obtain rfl : m = n + 2 := le_antisymm hmn h
      rw [Finset.prod_range_succ, pow_succ]
      calc |ξ| ^ (n + 1) * |ξ| * (‖𝓕 (KC a r n) ξ‖ * ‖khat (a (n + 1)) (r (n + 1)) ξ‖)
          = (|ξ| ^ (n + 1) * ‖𝓕 (KC a r n) ξ‖) * (|ξ| * ‖khat (a (n + 1)) (r (n + 1)) ξ‖) := by
            ring
        _ ≤ (∏ j ∈ Finset.range (n + 1), (a j / π)) * (a (n + 1) / π) :=
            mul_le_mul (ih (n + 1) le_rfl) (abs_mul_norm_khat_le (ha _) (hr _) ξ)
              (by positivity) (Finset.prod_nonneg fun j _ => div_nonneg (ha j).le pi_pos.le)
end GroundTheory.Automorphic.LineKernel
