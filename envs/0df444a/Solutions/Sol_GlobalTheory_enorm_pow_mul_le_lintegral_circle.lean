-- Prove2me | solution 1 for GlobalTheory.enorm_pow_mul_le_lintegral_circle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:37:08.796275+00:00
-- url     : https://prove2.me/submissions/7c076e12-18df-4a97-9d80-95cd02c578f8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EnormPowLeInvMeasureMulLintegralBall

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
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
namespace GlobalTheory
theorem _root_.solution {f : ℂ → H} (hf : DiffContOnCl ℂ f (ball 0 1)) (n : ℕ) :
    ‖f 0‖ₑ ^ n * ENNReal.ofReal (2 * π) ≤
      ∫⁻ t in Ioc 0 (2 * π), ‖f (circleMap 0 1 t)‖ₑ ^ n := by
  have h2 : (0 : ℝ) < 2 * π := by positivity
  have hc : Continuous fun t => f (circleMap 0 1 t) := by
    refine hf.continuousOn.comp_continuous (continuous_circleMap 0 1) fun t => ?_
    rw [closure_ball _ one_ne_zero]
    exact sphere_subset_closedBall (circleMap_mem_sphere 0 zero_le_one t)
  have hav : ⨍ t in Ioc 0 (2 * π), f (circleMap 0 1 t) = f 0 := by
    have h := DiffContOnCl.circleAverage (f := f) (c := 0) (R := 1) (by simpa using hf)
    rw [← h, Real.circleAverage, intervalIntegral.integral_of_le h2.le, setAverage_eq]
    simp [h2.le]
  have hg : ConvexOn ℝ univ fun x : H => ‖x‖ ^ n :=
    (convexOn_univ_norm (E := H)).pow (fun x _ => norm_nonneg x) n
  have hi : IntegrableOn (fun t => ‖f (circleMap 0 1 t)‖ ^ n) (Ioc 0 (2 * π)) :=
    (hc.norm.pow n).integrableOn_Ioc
  have hJ := hg.map_set_average_le (μ := volume) (t := Ioc 0 (2 * π))
    (f := fun t => f (circleMap 0 1 t)) (by fun_prop) isClosed_univ (by simp [Real.pi_pos])
    measure_Ioc_lt_top.ne (by simp) hc.integrableOn_Ioc hi
  rw [hav, setAverage_eq] at hJ
  simp only [Real.volume_real_Ioc, sub_zero, max_eq_left h2.le, smul_eq_mul] at hJ
  rw [le_inv_mul_iff₀ h2] at hJ
  have hl : ∫⁻ t in Ioc 0 (2 * π), ‖f (circleMap 0 1 t)‖ₑ ^ n =
      ENNReal.ofReal (∫ t in Ioc 0 (2 * π), ‖f (circleMap 0 1 t)‖ ^ n) := by
    rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun t => by positivity)]
    simp [ENNReal.ofReal_pow]
  rw [hl, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_mul (by positivity), mul_comm]
  exact ENNReal.ofReal_le_ofReal hJ
end GlobalTheory
