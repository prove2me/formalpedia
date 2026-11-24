-- Prove2me | solution 1 for GlobalTheory.taylorTail_step_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:36:59.730667+00:00
-- url     : https://prove2.me/submissions/8a6f60b5-6c9f-4998-aa31-204dc26c1e33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormLeLintegralTaylorTailIteratedDeriv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Set Module
open scoped ENNReal
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (g : ℝ → F) (a : ℝ) (hg : Differentiable ℝ g) (hd : Continuous (deriv g))
    (hlim : Tendsto g atTop (𝓝 0)) :
    ENNReal.ofReal ‖g a‖ ≤ ∫⁻ t in Ioi a, ‖deriv g t‖ₑ := by
  by_cases hI : IntegrableOn (deriv g) (Ioi a)
  · have hint : ∫ x in Ioi a, deriv g x = 0 - g a :=
      integral_Ioi_of_hasDerivAt_of_tendsto hg.continuous.continuousWithinAt
        (fun x _ => (hg x).hasDerivAt) hI hlim
    rw [zero_sub] at hint
    have h1 : ‖g a‖ ≤ ∫ x in Ioi a, ‖deriv g x‖ := by
      calc ‖g a‖ = ‖∫ x in Ioi a, deriv g x‖ := by rw [hint, norm_neg]
        _ ≤ ∫ x in Ioi a, ‖deriv g x‖ := norm_integral_le_integral_norm _
    calc ENNReal.ofReal ‖g a‖ ≤ ENNReal.ofReal (∫ x in Ioi a, ‖deriv g x‖) := ENNReal.ofReal_le_ofReal h1
      _ = ∫⁻ t in Ioi a, ‖deriv g t‖ₑ := ofReal_integral_norm_eq_lintegral_enorm hI
  · have : ∫⁻ t in Ioi a, ‖deriv g t‖ₑ = ∞ := by
      by_contra hne
      exact hI ⟨hd.aestronglyMeasurable, lt_top_iff_ne_top.mpr hne⟩
    rw [this]; exact le_top
end GlobalTheory
