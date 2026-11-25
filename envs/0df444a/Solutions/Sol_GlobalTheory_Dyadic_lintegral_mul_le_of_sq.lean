-- Prove2me | solution 1 for GlobalTheory.Dyadic.lintegral_mul_le_of_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:34:24.463834+00:00
-- url     : https://prove2.me/submissions/e519e9eb-c923-43ac-b995-f19a3f9df817

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LintegralBoundByDyadicSummation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
open GlobalTheory GlobalTheory.Dyadic
namespace GlobalTheory.Dyadic
theorem _root_.solution {X : Type} [MeasurableSpace X] (μ : Measure X) (A B : X → ℝ)
    (hA : Measurable A) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (h1 : ∫⁻ x, ENNReal.ofReal (A x ^ 2) ∂μ ≤ ENNReal.ofReal (α ^ 2))
    (h2 : ∫⁻ x, ENNReal.ofReal (B x ^ 2) ∂μ ≤ ENNReal.ofReal (β ^ 2)) :
    ∫⁻ x, ENNReal.ofReal (A x * B x) ∂μ ≤ ENNReal.ofReal (α * β) := by
  have hc : 0 ≤ β / (2 * α) := by positivity
  have hd : 0 ≤ α / (2 * β) := by positivity
  calc ∫⁻ x, ENNReal.ofReal (A x * B x) ∂μ
      ≤ ∫⁻ x, (ENNReal.ofReal (β / (2 * α)) * ENNReal.ofReal (A x ^ 2)
          + ENNReal.ofReal (α / (2 * β)) * ENNReal.ofReal (B x ^ 2)) ∂μ := by
        refine lintegral_mono fun x => ?_
        rw [← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_mul hd,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have : β / (2 * α) * A x ^ 2 + α / (2 * β) * B x ^ 2 - A x * B x
            = (β * A x - α * B x) ^ 2 / (2 * α * β) := by
          field_simp; ring
        have h3 : 0 ≤ (β * A x - α * B x) ^ 2 / (2 * α * β) := by positivity
        linarith
    _ = ENNReal.ofReal (β / (2 * α)) * ∫⁻ x, ENNReal.ofReal (A x ^ 2) ∂μ
          + ENNReal.ofReal (α / (2 * β)) * ∫⁻ x, ENNReal.ofReal (B x ^ 2) ∂μ := by
        rw [lintegral_add_left (by fun_prop), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (β / (2 * α)) * ENNReal.ofReal (α ^ 2)
          + ENNReal.ofReal (α / (2 * β)) * ENNReal.ofReal (β ^ 2) := by gcongr
    _ = ENNReal.ofReal (α * β) := by
        rw [← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_mul hd,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        field_simp; ring
end GlobalTheory.Dyadic
