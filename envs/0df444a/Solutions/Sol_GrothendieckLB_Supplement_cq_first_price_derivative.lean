-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_first_price_derivative
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T22:04:08.202834+00:00
-- url     : https://prove2.me/submissions/c6b800fe-d09c-4743-becd-e0248d87d43a

import Theorems.Thm_GrothendieckLB_Supplement_cq_threshold_real_representation
import Theorems.Thm_GrothendieckLB_Supplement_cq_threshold_integral_derivative
import Definitions.Def_GrothendieckLB_Supplement_cqThresholdKernel
import Definitions.Def_GrothendieckLB_Supplement_cqCorr
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic.Linarith

open GrothendieckLB.Supplement Filter
open scoped Topology
namespace CQThresholdContinuation
theorem apply_to (hrep : ∀ t : ℝ, |t|<1 → CQThreshold.H t=(cqCorr 0.136419125 0.34101124 0.05276111 t:ℂ))
    (hder : ∀ z : ℂ, ‖z‖<1 → HasDerivAt CQThreshold.H
      (deriv (CQPrice.eval CQPrice.rho) z * CQPrice.partialTerm z 1 0 - CQPrice.partialTerm z 0 1) z)
    (F : ℂ→ℂ) (hF : DifferentiableOn ℂ F (Metric.ball 0 1))
    (hreal : ∀ t : ℝ, |t|<1 → F (t:ℂ)=(cqCorr 0.136419125 0.34101124 0.05276111 t:ℂ))
    (z : ℂ) (hz : ‖z‖<1) : HasDerivAt F
      (deriv (CQPrice.eval CQPrice.rho) z * CQPrice.partialTerm z 1 0 - CQPrice.partialTerm z 0 1) z := by
  have hH : DifferentiableOn ℂ CQThreshold.H (Metric.ball 0 1) := fun w hw =>
    (hder w (by simpa using hw)).differentiableAt.differentiableWithinAt
  have hclosure : (0:ℂ) ∈ closure ({w : ℂ | F w=CQThreshold.H w} \ {(0:ℂ)}) := by
    apply Metric.mem_closure_iff.mpr
    intro e he
    let t := min (e/2) (1/2:ℝ)
    have ht : 0<t := lt_min (by positivity) (by norm_num)
    have ht' : |t|<1 := by rw [abs_of_pos ht];exact (min_le_right _ _).trans_lt (by norm_num)
    have het : t<e := (min_le_left _ _).trans_lt (by linarith)
    exact ⟨(t:ℂ),⟨(hreal t ht').trans (hrep t ht').symm,by simpa using ht.ne'⟩,by simpa [abs_of_pos ht] using het⟩
  have heq := (hF.analyticOnNhd Metric.isOpen_ball).eqOn_of_preconnected_of_mem_closure
    (hH.analyticOnNhd Metric.isOpen_ball) (convex_ball (0:ℂ) (1:ℝ)).isPreconnected
    (by simp : (0:ℂ)∈Metric.ball 0 1) hclosure
  exact (hder z hz).congr_of_eventuallyEq (heq.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds (by simpa using hz)))
end CQThresholdContinuation

open GrothendieckLB.Supplement

theorem solution (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (Metric.ball 0 1))
    (hreal : ∀ t : ℝ, |t|<1 → F (t:ℂ)=(cqCorr 0.136419125 0.34101124 0.05276111 t:ℂ))
    (z : ℂ) (hz : ‖z‖<1) :
    HasDerivAt F (deriv (CQPrice.eval CQPrice.rho) z * CQPrice.partialTerm z 1 0 - CQPrice.partialTerm z 0 1) z := CQThresholdContinuation.apply_to cq_threshold_real_representation cq_threshold_integral_derivative F hF hreal z hz
