-- Prove2me | solution 1 for OAI.MetricKMedian.PhysicalPotential.time_increase_le_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T11:06:27.238424+00:00
-- url     : https://prove2.me/submissions/5540608a-a1bf-4168-844d-e403537ff571

import Mathlib
import Definitions.Def_OAIQ035K021

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_MomentAnalysis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Analytic

open MeasureTheory Set Filter
open scoped Topology Filter Interval

theorem moment_integrable (n : ℕ) (x : ℝ) :
    IntervalIntegrable (fun t : ℝ => t^n*Real.exp (-t*x)) volume 0 1 := by
  apply Continuous.intervalIntegrable
  fun_prop

private theorem kernel_deriv (n : ℕ) (t x : ℝ) :
    HasDerivAt (fun z : ℝ => t^n*Real.exp (-t*z)) (-t^(n+1)*Real.exp (-t*x)) x := by
  have h := (((hasDerivAt_id x).const_mul (-t)).exp).const_mul (t^n)
  convert h using 1 <;> try rfl
  simp only [id_eq, mul_one, pow_succ]
  ring

theorem hasDerivAt_moment (n : ℕ) (x : ℝ) :
    HasDerivAt (moment n) (-moment (n+1) x) x := by
  have hmeas : ∀ᶠ z : ℝ in 𝓝 x,
      AEStronglyMeasurable (fun t : ℝ => t^n*Real.exp (-t*z)) (volume.restrict (Ι 0 1)) := by
    apply Filter.Eventually.of_forall
    intro z
    exact (show Continuous (fun t : ℝ => t^n*Real.exp (-t*z)) by fun_prop).aestronglyMeasurable
  have hmeas' : AEStronglyMeasurable (fun t : ℝ => -t^(n+1)*Real.exp (-t*x))
      (volume.restrict (Ι 0 1)) := by
    exact (show Continuous (fun t : ℝ => -t^(n+1)*Real.exp (-t*x)) by fun_prop).aestronglyMeasurable
  have hbound : ∀ᵐ t : ℝ ∂volume, t ∈ Ι (0:ℝ) 1 →
      ∀ z ∈ Metric.ball x 1, ‖-t^(n+1)*Real.exp (-t*z)‖ ≤ Real.exp (|x|+1) := by
    apply Filter.Eventually.of_forall
    intro t ht z hz
    have ht' : 0 ≤ t ∧ t ≤ 1 := by
      simp only [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1), mem_Ioc] at ht
      exact ⟨ht.1.le, ht.2⟩
    have hz' : |z-x| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using hz
    have hab : |z| ≤ |x|+1 := by
      have hh := abs_add_le (z-x) x
      rw [sub_add_cancel] at hh
      linarith
    have hexp : -t*z ≤ |x|+1 := by
      have ha := mul_le_mul_of_nonneg_left (neg_le_abs z) ht'.1
      have hb := mul_le_of_le_one_left (abs_nonneg z) ht'.2
      nlinarith only [ha, hb, hab]
    have hpow : t^(n+1) ≤ 1 := pow_le_one₀ ht'.1 ht'.2
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg (pow_nonneg ht'.1 _),
      abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le).trans
      (by simpa only [one_mul] using Real.exp_le_exp.mpr hexp)
  have hdiff : ∀ᵐ t : ℝ ∂volume, t ∈ Ι (0:ℝ) 1 →
      ∀ z ∈ Metric.ball x 1, HasDerivAt (fun z : ℝ => t^n*Real.exp (-t*z))
        (-t^(n+1)*Real.exp (-t*z)) z := by
    exact Filter.Eventually.of_forall (fun t _ z _ => kernel_deriv n t z)
  have h := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds x (by norm_num : (0:ℝ) < 1)) hmeas (moment_integrable n x)
    hmeas' hbound (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => Real.exp (|x|+1)) volume 0 1)
    hdiff).2
  change HasDerivAt (fun z => ∫ t : ℝ in 0..1, t^n*Real.exp (-t*z))
    (-(∫ t : ℝ in 0..1, t^(n+1)*Real.exp (-t*x))) x
  simpa only [neg_mul, intervalIntegral.integral_neg] using h

theorem moment_nonneg (n : ℕ) (x : ℝ) : 0 ≤ moment n x := by
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro t ht
  exact mul_nonneg (pow_nonneg ht.1 n) (Real.exp_pos _).le

theorem moment_le_one (n : ℕ) {x : ℝ} (hx0 : 0 ≤ x) : moment n x ≤ 1 := by
  have h := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
    (moment_integrable n x) (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1:ℝ)) volume 0 1)
    (fun t (ht : t ∈ Icc (0:ℝ) 1) => show t^n*Real.exp (-t*x) ≤ (1:ℝ) from by
      have hpow : t^n ≤ 1 := pow_le_one₀ ht.1 ht.2
      have he : Real.exp (-t*x) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg ht.1 hx0])
      exact (mul_le_of_le_one_left (Real.exp_pos _).le hpow).trans he)
  simpa only [moment, intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_mul] using h

theorem P_eq_moment (x : ℝ) : P x = moment 1 x := by simp only [P, moment, pow_one]

theorem A_eq_moment (x : ℝ) : A x = 3-2*moment 0 x := by
  unfold A moment
  rw [intervalIntegral.integral_sub intervalIntegrable_const (by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [pow_zero, one_mul, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  ring

theorem hasDerivAt_A (x : ℝ) : HasDerivAt A (B x) x := by
  have h := ((hasDerivAt_moment 0 x).const_mul 2).const_sub 3
  have hd : HasDerivAt (fun z : ℝ => 3-2*moment 0 z) (B x) x := by
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    simp only [B, P_eq_moment, Nat.zero_add]
    ring
  exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall A_eq_moment)

theorem hasDerivAt_B (x : ℝ) : HasDerivAt B (-2*moment 2 x) x := by
  have h := (hasDerivAt_moment 1 x).const_mul 2
  have he : B = fun z => 2*moment 1 z := by funext z; simp only [B, P_eq_moment]
  rw [he]
  simpa only [neg_mul, mul_neg] using h

theorem coefficient_eq (x y : ℝ) : coefficient x y = 1+m x+B x*y := by
  unfold coefficient m B
  ring

theorem hasDerivAt_coefficient (x y : ℝ) :
    HasDerivAt (fun z => coefficient z y) (-2*(y-x)*moment 2 x) x := by
  have h := (hasDerivAt_A x).add ((hasDerivAt_B x).mul ((hasDerivAt_const x y).sub (hasDerivAt_id x)))
  change HasDerivAt (fun z => A z+B z*(y-z)) _ x
  convert h using 1 <;> try rfl
  dsimp only [id_eq, Pi.sub_apply]
  ring

end MetricKMedian.Analytic
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_PhysicalPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.PhysicalPotential

open Analytic

variable {I : Type*}

theorem mass_nonneg {g : ℝ} (hg : 0 ≤ g) (S : Finset I) : 0 ≤ mass g S := by
  exact mul_nonneg hg (Nat.cast_nonneg _)

theorem cost_nonneg {g : ℝ} {d : I → ℝ} {S : Finset I} (hg : 0 ≤ g)
    (hd : ∀ i ∈ S, 0 ≤ d i) : 0 ≤ cost g d S := by
  exact Finset.sum_nonneg (fun i hi => mul_nonneg hg (hd i hi))

end MetricKMedian.PhysicalPotential
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_TimeAdvance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Analytic
open Set

 theorem hasDerivAt_timeRate (x y : ℝ) :
    HasDerivAt (fun z => timeRate z y) (rateDerivative x y) x := by
  have h := (((hasDerivAt_id x).const_mul 2).mul
    ((hasDerivAt_const x y).sub (hasDerivAt_id x))).mul (hasDerivAt_moment 2 x)
  convert h using 1 <;> try rfl
  dsimp only [rateDerivative, id_eq, Pi.sub_apply, Pi.mul_apply]
  norm_num only [Nat.reduceAdd]
  ring

theorem abs_timeRate {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : |timeRate x y| ≤ 2 := by
  have hdiff : |y-x| ≤ 1 := abs_le.mpr ⟨by linarith only [hy0, hx1], by linarith only [hy1, hx0]⟩
  have hm0 := moment_nonneg 2 x
  have hm1 := moment_le_one 2 hx0
  rw [timeRate, abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
    abs_of_nonneg hx0, abs_of_nonneg hm0]
  have hprod : x*|y-x| ≤ 1 := (mul_le_of_le_one_left (abs_nonneg _) hx1).trans hdiff
  have h := mul_le_mul hprod hm1 hm0 (by norm_num : (0:ℝ) ≤ 1)
  nlinarith only [h]

theorem abs_rateDerivative {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : |rateDerivative x y| ≤ 6 := by
  have hdiff : |y-x| ≤ 1 := abs_le.mpr ⟨by linarith only [hy0, hx1], by linarith only [hy1, hx0]⟩
  have hdiff2 : |y-2*x| ≤ 2 := abs_le.mpr ⟨by linarith only [hy0, hx1], by linarith only [hy1, hx0]⟩
  have hm20 := moment_nonneg 2 x
  have hm21 := moment_le_one 2 hx0
  have hm30 := moment_nonneg 3 x
  have hm31 := moment_le_one 3 hx0
  have hfirst : |2*(y-2*x)*moment 2 x| ≤ 4 := by
    have h := mul_le_mul hdiff2 hm21 hm20 (by norm_num : (0:ℝ) ≤ 2)
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_of_nonneg hm20]
    nlinarith only [h]
  have hsecond : |2*x*(y-x)*moment 3 x| ≤ 2 := by
    have hp := (mul_le_of_le_one_left (abs_nonneg (y-x)) hx1).trans hdiff
    have h := mul_le_mul hp hm31 hm30 (by norm_num : (0:ℝ) ≤ 1)
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
      abs_of_nonneg hx0, abs_of_nonneg hm30]
    nlinarith only [h]
  exact (abs_sub _ _).trans (by linarith only [hfirst, hsecond])

theorem taylor_error_bound (f f' f'' : ℝ → ℝ) {h C : ℝ}
    (hh : 0 ≤ h) (hC : 0 ≤ C)
    (hf : ∀ t ∈ Icc 0 h, HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Icc 0 h, HasDerivAt f' (f'' t) t)
    (hb : ∀ t ∈ Icc 0 h, |f'' t| ≤ C) :
    |f h-f 0-h*f' 0| ≤ C*h^2 := by
  have hr : ∀ t ∈ Icc 0 h, |f' t-f' 0| ≤ C*h := by
    intro t ht
    have hl := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun t ht => (hf' t ht).hasDerivWithinAt)
      (fun t ht => show ‖f'' t‖ ≤ C from by simpa only [Real.norm_eq_abs] using hb t ⟨ht.1, ht.2.le⟩)
      t ht
    simp only [Real.norm_eq_abs, sub_zero] at hl
    exact hl.trans (mul_le_mul_of_nonneg_left ht.2 hC)
  let r := fun t : ℝ => f t-f 0-t*f' 0
  have hdr : ∀ t ∈ Icc 0 h, HasDerivAt r (f' t-f' 0) t := by
    intro t ht
    convert ((hf t ht).sub_const (f 0)).sub ((hasDerivAt_id t).mul_const (f' 0)) using 1 <;> first | rfl | simp only [one_mul]
  have hd := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun t ht => (hdr t ht).hasDerivWithinAt)
    (fun t ht => show ‖f' t-f' 0‖ ≤ C*h from by simpa only [Real.norm_eq_abs] using hr t ⟨ht.1, ht.2.le⟩)
    h ⟨hh, le_refl _⟩
  simpa only [r, sub_self, zero_mul, sub_zero, Real.norm_eq_abs, pow_two, mul_assoc] using hd

 theorem hasDerivAt_phase (x t : ℝ) :
    HasDerivAt (fun u : ℝ => x*Real.exp (-u)) (-(x*Real.exp (-t))) t := by
  simpa only [neg_mul, mul_neg, mul_one, Pi.neg_apply, id_eq] using (((hasDerivAt_id t).neg).exp).const_mul x

 theorem phase_bounds {x t : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (ht : 0 ≤ t) :
    0 ≤ x*Real.exp (-t) ∧ x*Real.exp (-t) ≤ 1 := by
  refine ⟨mul_nonneg hx0 (Real.exp_pos _).le, ?_⟩
  exact (mul_le_of_le_one_left (Real.exp_pos _).le hx1).trans
    (Real.exp_le_one_iff.mpr (by linarith only [ht]))

 theorem hasDerivAt_timeCoefficient (x y t : ℝ) :
    HasDerivAt (fun u => coefficient (x*Real.exp (-u)) y)
      (timeRate (x*Real.exp (-t)) y) t := by
  have h := (hasDerivAt_coefficient (x*Real.exp (-t)) y).comp t (hasDerivAt_phase x t)
  convert h using 1 <;> try rfl
  dsimp only [timeRate]
  ring

theorem coefficient_time_error {x y h : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hh : 0 ≤ h) :
    |coefficient (x*Real.exp (-h)) y-coefficient x y-h*timeRate x y| ≤ 6*h^2 := by
  have hdr : ∀ t ∈ Icc (0:ℝ) h,
      HasDerivAt (fun u => timeRate (x*Real.exp (-u)) y)
        (rateDerivative (x*Real.exp (-t)) y * (-(x*Real.exp (-t)))) t := by
    intro t _
    exact (hasDerivAt_timeRate (x*Real.exp (-t)) y).comp t (hasDerivAt_phase x t)
  have hb : ∀ t ∈ Icc (0:ℝ) h,
      |rateDerivative (x*Real.exp (-t)) y * (-(x*Real.exp (-t)))| ≤ 6 := by
    intro t ht
    have hx := phase_bounds hx0 hx1 ht.1
    rw [abs_mul, abs_neg, abs_of_nonneg hx.1]
    exact (mul_le_mul (abs_rateDerivative hx.1 hx.2 hy0 hy1) hx.2 hx.1
      (by norm_num : (0:ℝ) ≤ 6)).trans (by norm_num)
  have he := taylor_error_bound (fun u => coefficient (x*Real.exp (-u)) y)
    (fun u => timeRate (x*Real.exp (-u)) y)
    (fun t => rateDerivative (x*Real.exp (-t)) y * (-(x*Real.exp (-t)))) hh
    (by norm_num) (fun t _ => hasDerivAt_timeCoefficient x y t) hdr hb
  simpa only [neg_zero, Real.exp_zero, mul_one] using he

end MetricKMedian.Analytic

namespace MetricKMedian.PhysicalPotential
open Analytic
variable {I : Type*}

 theorem potential_time_error {x g b h : ℝ} {d : I → ℝ} {S : Finset I}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hg : 0 ≤ g)
    (hd : ∀ i ∈ S, 0 ≤ d i) (hy : mass g S ≤ 1) (hh : 0 ≤ h) :
    |potential (x*Real.exp (-h)) g d S b-potential x g d S b-
      h*timeRate x (mass g S)*cost g d S| ≤ 6*h^2*cost g d S := by
  have he := mul_le_mul_of_nonneg_right
    (coefficient_time_error hx0 hx1 (mass_nonneg hg S) hy hh) (cost_nonneg hg hd)
  have hid : potential (x*Real.exp (-h)) g d S b-potential x g d S b-
      h*timeRate x (mass g S)*cost g d S =
      (coefficient (x*Real.exp (-h)) (mass g S)-coefficient x (mass g S)-h*timeRate x (mass g S))*cost g d S := by
    simp only [potential, coefficient_eq]
    ring
  rw [hid, abs_mul, abs_of_nonneg (cost_nonneg hg hd)]
  exact he

end MetricKMedian.PhysicalPotential
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_ForceBatchBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.PhysicalPotential
open Analytic
variable {I : Type*}

theorem time_increase_le_s35_oai {x g h b : ℝ} {d : I → ℝ} {S : Finset I}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hg : 0 ≤ g) (hh : 0 ≤ h)
    (hd0 : ∀ i ∈ S, 0 ≤ d i) (hy : mass g S ≤ 1) :
    potential (x*Real.exp (-h)) g d S b-potential x g d S b ≤
      (2*h+6*h^2)*cost g d S := by
  have he := potential_time_error (b := b) hx0 hx1 hg hd0 hy hh
  have hr := (abs_le.mp (abs_timeRate hx0 hx1 (mass_nonneg hg S) hy)).2
  have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr hh) (cost_nonneg hg hd0)
  have ht := (le_abs_self _).trans he
  nlinarith only [ht, hm]

end MetricKMedian.PhysicalPotential

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedian.PhysicalPotential.time_increase_le_s35_oai.{u_1} := @OAI.MetricKMedian.PhysicalPotential.time_increase_le_s35_oai.{u_1}
