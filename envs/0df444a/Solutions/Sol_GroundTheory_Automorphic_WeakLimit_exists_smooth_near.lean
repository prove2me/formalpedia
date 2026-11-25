-- Prove2me | solution 1 for GroundTheory.Automorphic.WeakLimit.exists_smooth_near
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:01:23.320667+00:00
-- url     : https://prove2.me/submissions/525ee6db-30c0-4681-b04c-9c30a5e9adba

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineLimit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Filter Topology Set
open scoped FourierTransform ContDiff
open GroundTheory.Automorphic.WeakLimit
namespace GroundTheory.Automorphic.WeakLimit
theorem _root_.solution (a b : ℝ) {ψ : ℝ → ℂ} (hψ : Continuous ψ) {η : ℝ} (hη : 0 < η) :
    ∃ ψ' : ℝ → ℂ, ContDiff ℝ ∞ ψ' ∧ HasCompactSupport ψ' ∧ ∀ t ∈ Icc a b, ‖ψ t - ψ' t‖ ≤ η := by
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn a b (fun t => (ψ t).re)
    (Complex.continuous_re.comp hψ).continuousOn (η / 2) (by positivity)
  obtain ⟨q, hq⟩ := exists_polynomial_near_of_continuousOn a b (fun t => (ψ t).im)
    (Complex.continuous_im.comp hψ).continuousOn (η / 2) (by positivity)
  have hpd : ∀ r : Polynomial ℝ, ContDiff ℝ ∞ (fun t : ℝ => r.eval t) := fun r => by
    simpa [Polynomial.coe_aeval_eq_eval] using r.contDiff_aeval (𝕜 := ℝ) ∞
  let χ : ContDiffBump ((a + b) / 2) := ⟨|b - a| + 1, |b - a| + 2, by positivity, by linarith⟩
  refine ⟨fun t => (χ t : ℂ) * (((p.eval t : ℝ) : ℂ) + ((q.eval t : ℝ) : ℂ) * Complex.I), ?_, ?_, ?_⟩
  · exact (Complex.ofRealCLM.contDiff.comp χ.contDiff).mul
      ((Complex.ofRealCLM.contDiff.comp (hpd p)).add
        ((Complex.ofRealCLM.contDiff.comp (hpd q)).mul contDiff_const))
  · exact (χ.hasCompactSupport.comp_left Complex.ofReal_zero).mul_right
  · intro t ht
    have hχ : χ t = 1 := by
      apply χ.one_of_mem_closedBall
      rw [Metric.mem_closedBall, Real.dist_eq]
      have := ht.1; have := ht.2
      rw [abs_le]; constructor <;> cases abs_cases (b - a) <;> linarith
    show ‖ψ t - (χ t : ℂ) * _‖ ≤ η
    rw [hχ, Complex.ofReal_one, one_mul]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have h1 := hp t ht
    have h2 := hq t ht
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, Complex.sub_im, Complex.add_im, Complex.mul_im, mul_zero,
      mul_one, sub_zero, add_zero, zero_add]
    rw [abs_sub_comm] at h1 h2
    linarith
end GroundTheory.Automorphic.WeakLimit
