-- Prove2me | solution 1 for GlobalTheory.DirichletTail.LFunction_eq_tsum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:45:09.695124+00:00
-- url     : https://prove2.me/submissions/ccf626e4-3c54-44f6-837f-788ae922033e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LFunctionEqTsumOfOneLt
import Theorems.Thm_GlobalTheory_DirichletTail_hasSum_telescope
import Theorems.Thm_GlobalTheory_DirichletTail_norm_term_le
import Theorems.Thm_GlobalTheory_DirichletTail_LFunction_eq_tsum_of_one_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.DirichletTail
open Filter Topology
namespace GlobalTheory.DirichletTail
theorem _root_.solution {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) : LFunction χ s = ∑' n, term χ n s := by
  have hUo : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hc : ∀ m : ℕ, Differentiable ℂ (fun w : ℂ ↦ ((m + 1 : ℕ) : ℂ) ^ (-w)) := fun m w ↦
    differentiableAt_id.neg.const_cpow (Or.inl (by exact_mod_cast Nat.succ_ne_zero m))
  have hd : DifferentiableOn ℂ (fun z ↦ ∑' n, term χ n z) {z : ℂ | 0 < z.re} := by
    intro z hz
    have hz' : 0 < z.re := hz
    have hVo : IsOpen ({w : ℂ | z.re / 2 < w.re} ∩ Metric.ball 0 (‖z‖ + 1)) :=
      (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
    have hzV : z ∈ {w : ℂ | z.re / 2 < w.re} ∩ Metric.ball 0 (‖z‖ + 1) :=
      ⟨show z.re / 2 < z.re by linarith, by simp⟩
    have hsum : Summable (fun n : ℕ ↦ (q : ℝ) * ((‖z‖ + 1) / (z.re / 2)) *
        (((n + 1 : ℕ) : ℝ) ^ (-(z.re / 2)) - ((n + 1 + 1 : ℕ) : ℝ) ^ (-(z.re / 2)))) :=
      ((hasSum_telescope (half_pos hz') 0).summable.mul_left
        ((q : ℝ) * ((‖z‖ + 1) / (z.re / 2)))).congr fun n ↦ by
        simp only [add_zero]
    have hdiff : ∀ n : ℕ, DifferentiableOn ℂ (fun w ↦ term χ n w)
        ({w : ℂ | z.re / 2 < w.re} ∩ Metric.ball 0 (‖z‖ + 1)) := fun n ↦
      ((differentiable_const _).mul ((hc n).sub (hc (n + 1)))).differentiableOn
    have := differentiableOn_tsum_of_summable_norm hsum hdiff hVo fun n w hw ↦
      norm_term_le χ hχ n (half_pos hz') hw.1.le (mem_ball_zero_iff.mp hw.2).le
    exact ((this z hzV).differentiableAt (hVo.mem_nhds hzV)).differentiableWithinAt
  have hL := ((differentiable_LFunction hχ).differentiableOn (s := {z : ℂ | 0 < z.re})).analyticOnNhd hUo
  have hT := hd.analyticOnNhd hUo
  have h2 : (2 : ℂ) ∈ {z : ℂ | 0 < z.re} := by simp
  have hev : LFunction χ =ᶠ[𝓝 (2 : ℂ)] fun z ↦ ∑' n, term χ n z := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by simp)] with z hz
    exact LFunction_eq_tsum_of_one_lt χ hχ hz
  exact hL.eqOn_of_preconnected_of_eventuallyEq hT (convex_halfSpace_re_gt 0).isPreconnected h2 hev hs
end GlobalTheory.DirichletTail
