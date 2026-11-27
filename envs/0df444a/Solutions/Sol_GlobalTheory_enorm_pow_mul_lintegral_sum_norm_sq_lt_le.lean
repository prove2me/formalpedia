-- Prove2me | solution 1 for GlobalTheory.enorm_pow_mul_lintegral_sum_norm_sq_lt_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:37:41.516294+00:00
-- url     : https://prove2.me/submissions/8e3c7683-94f1-4190-9f4c-468c15d88e98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EnormPowLeInvMeasureMulLintegralBall
import Theorems.Thm_GlobalTheory_enorm_pow_mul_lintegral_le_of_balanced

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set
open scoped ENNReal Real
open GlobalTheory
variable {ι : Type*} [Fintype ι]
namespace GlobalTheory
theorem _root_.solution {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℂ H] [CompleteSpace H] {R : ℝ} {φ : (ι → ℂ) → H}
    (hφ : DifferentiableOn ℂ φ {x | ∑ i, ‖x i‖ ^ 2 < R}) {w : ℝ → ℝ≥0∞} (hw : Measurable w)
    (n : ℕ) :
    ‖φ 0‖ₑ ^ n * ∫⁻ z in {x : ι → ℂ | ∑ i, ‖x i‖ ^ 2 < R}, w (∑ i, ‖z i‖ ^ 2) ≤
      ∫⁻ z in {x : ι → ℂ | ∑ i, ‖x i‖ ^ 2 < R}, ‖φ z‖ₑ ^ n * w (∑ i, ‖z i‖ ^ 2) := by
  have hq : Continuous fun x : ι → ℂ => ∑ i, ‖x i‖ ^ 2 := by fun_prop
  have ho : IsOpen {x : ι → ℂ | ∑ i, ‖x i‖ ^ 2 < R} := isOpen_lt hq continuous_const
  refine enorm_pow_mul_lintegral_le_of_balanced volume ho.measurableSet ?_
    (fun _ hz => hφ.differentiableAt (ho.mem_nhds hz)) (w := fun z => w (∑ i, ‖z i‖ ^ 2))
    (hw.comp hq.measurable) (fun c hc z _ => by simp [hc]) n
  rintro c hc _ ⟨z, hz, rfl⟩
  simp only [mem_ofPred_eq, Pi.smul_apply, norm_smul] at hz ⊢
  refine lt_of_le_of_lt (Finset.sum_le_sum fun i _ => ?_) hz
  gcongr
  exact mul_le_of_le_one_left (norm_nonneg _) hc
end GlobalTheory
