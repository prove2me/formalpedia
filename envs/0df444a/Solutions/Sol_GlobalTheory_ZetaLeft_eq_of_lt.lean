-- Prove2me | solution 1 for GlobalTheory.ZetaLeft.eq_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:50:07.613848+00:00
-- url     : https://prove2.me/submissions/64863ca5-9528-4c28-83d5-d11a8b453ece

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormSubOneMulRiemannZetaLe
import Theorems.Thm_GlobalTheory_ZetaLeft_differentiable_emT
import Theorems.Thm_GlobalTheory_ZetaLeft_differentiableOn_tsum_emE
import Theorems.Thm_GlobalTheory_ZetaLeft_eq_of_one_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open Filter Topology
open GlobalTheory GlobalTheory.ZetaLeft
namespace GlobalTheory.ZetaLeft
theorem _root_.solution {s : ℂ} (hs : -(15/8 : ℝ) < s.re) (h1 : s ≠ 1) :
    (s - 1) * riemannZeta s = emT 1 s + ∑' n : ℕ, emE ((n : ℝ) + 1) s := by
  have ho : IsOpen {z : ℂ | -(15/8 : ℝ) < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hf : ∀ z : ℂ, z ≠ 1 → LFunctionTrivChar₁ 1 z = (z - 1) * riemannZeta z := by
    intro z hz
    rw [LFunctionTrivChar₁, Function.update_of_ne hz, LFunctionTrivChar, LFunction_modOne_eq]
  have hA : AnalyticOnNhd ℂ (LFunctionTrivChar₁ 1) {z : ℂ | -(15/8 : ℝ) < z.re} :=
    (differentiable_LFunctionTrivChar₁ 1).differentiableOn.analyticOnNhd ho
  have hB : AnalyticOnNhd ℂ (fun s => emT 1 s + ∑' n : ℕ, emE ((n : ℝ) + 1) s)
      {z : ℂ | -(15/8 : ℝ) < z.re} :=
    ((differentiable_emT one_pos).differentiableOn.add differentiableOn_tsum_emE).analyticOnNhd ho
  have := hA.eqOn_of_preconnected_of_eventuallyEq hB
    (convex_halfSpace_re_gt _).isPreconnected (z₀ := 2) (by simp; norm_num) (by
      have : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
        (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
      filter_upwards [this] with z hz
      rw [hf z (by rintro rfl; simp at hz), eq_of_one_lt hz])
  rw [← hf s h1]
  exact this hs
end GlobalTheory.ZetaLeft
