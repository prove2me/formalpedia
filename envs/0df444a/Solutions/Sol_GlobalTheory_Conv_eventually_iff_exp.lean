-- Prove2me | solution 1 for GlobalTheory.Conv.eventually_iff_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:36:57.204687+00:00
-- url     : https://prove2.me/submissions/036ce7be-a443-4f83-9e92-10254461aa4d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemPuncturedRingIffPowerSeriesPart
import Theorems.Thm_GlobalTheory_Conv_coe_expandConv
import Theorems.Thm_GlobalTheory_Conv_expandConv_u
import Theorems.Thm_GlobalTheory_Conv_coe_expandConvLaurent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Conv.coe_expandConv
attribute [local simp] GlobalTheory.Conv.expandConv_u
attribute [local simp] GlobalTheory.Conv.coe_expandConvLaurent

set_option autoImplicit false
open scoped PowerSeries LaurentSeries Topology ENNReal NNReal ContDiff
open Filter Metric
noncomputable section
open GlobalTheory GlobalTheory.Conv
namespace GlobalTheory.Conv
theorem _root_.solution {p : ℂ → Prop} :
    (∀ᶠ v in 𝓝[≠] (0 : ℂ), p v) ↔
      ∃ T : ℝ, ∀ w : ℂ, T < w.im → p (Complex.exp (2 * Real.pi * Complex.I * w)) := by
  have hn : ∀ w : ℂ, ‖Complex.exp (2 * Real.pi * Complex.I * w)‖ =
      Real.exp (-(2 * Real.pi * w.im)) := fun w => by
    rw [Complex.norm_exp]
    simp
  have hπ : 0 < 2 * Real.pi := by positivity
  rw [eventually_iff_exists_puncturedDisc]
  constructor
  · rintro ⟨ε, hε, h⟩
    refine ⟨-Real.log ε / (2 * Real.pi), fun w hw => h _
      (mem_puncturedDisc.2 ⟨Complex.exp_ne_zero _, ?_⟩)⟩
    rw [hn, ← Real.lt_log_iff_exp_lt hε]
    rw [div_lt_iff₀ hπ] at hw
    linarith
  · rintro ⟨T, h⟩
    refine ⟨Real.exp (-(2 * Real.pi * T)), Real.exp_pos _, fun v hv => ?_⟩
    obtain ⟨hv0, hv⟩ := mem_puncturedDisc.1 hv
    have hw : Complex.exp (2 * Real.pi * Complex.I *
        (Complex.log v / (2 * Real.pi * Complex.I))) = v := by
      rw [mul_div_cancel₀ _ Complex.two_pi_I_ne_zero, Complex.exp_log hv0]
    rw [← hw] at hv ⊢
    refine h _ ?_
    rw [hn, Real.exp_lt_exp, neg_lt_neg_iff] at hv
    exact lt_of_mul_lt_mul_left hv hπ.le
end GlobalTheory.Conv
