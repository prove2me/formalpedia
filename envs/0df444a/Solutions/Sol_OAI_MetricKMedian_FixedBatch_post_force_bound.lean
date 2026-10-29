-- Prove2me | solution 1 for OAI.MetricKMedian.FixedBatch.post_force_bound
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:08:19.868839+00:00
-- url     : https://prove2.me/submissions/2f27108e-c308-484f-a4c8-512b64f8aaef

import Mathlib
import Definitions.Def_OAIQ035K021

section

attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

section
namespace OAI.MetricKMedian.FiniteLaw
variable {Ω : Type*} [Fintype Ω]
theorem prob_mono (μ : FiniteLaw Ω) {E F : Ω → Prop} [DecidablePred E] [DecidablePred F]
    (hEF : ∀ ω, E ω → F ω) : μ.prob E ≤ μ.prob F := by
  apply μ.expect_mono
  intro ω
  split_ifs with he hf hf <;> try norm_num
  exact False.elim (hf (hEF ω he))

end OAI.MetricKMedian.FiniteLaw
end

section
namespace OAI.MetricKMedian.FiniteLaw
variable {Ω : Type*} [Fintype Ω]
theorem prob_exists_le_sum (μ : FiniteLaw Ω) {I : Type*} (s : Finset I)
    (E : I → Ω → Prop) [∀ i, DecidablePred (E i)] :
    μ.prob (fun ω => ∃ i ∈ s, E i ω) ≤ ∑ i ∈ s, μ.prob (E i) := by
  classical
  unfold prob
  rw [← expect_sum]
  apply μ.expect_mono
  intro ω
  by_cases h : ∃ i ∈ s, E i ω
  · obtain ⟨i, hi, hei⟩ := h
    simp only [ite_eq_left (show ∃ i ∈ s, E i ω from ⟨i, hi, hei⟩)]
    have hsingle := Finset.single_le_sum (f := fun j => if E j ω then (1:ℝ) else 0)
      (fun j _ => by split_ifs <;> norm_num) hi
    simpa only [ite_eq_left hei] using hsingle
  · simp only [ite_eq_right h]
    exact Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)

end OAI.MetricKMedian.FiniteLaw
end

section
namespace OAI.MetricKMedian.Analytic
theorem texp_integrable (x : ℝ) :
    IntervalIntegrable (fun t : ℝ => t * Real.exp (-t * x)) MeasureTheory.volume 0 1 := by
  apply Continuous.intervalIntegrable
  fun_prop

end OAI.MetricKMedian.Analytic
end

section
namespace OAI.MetricKMedian.Analytic
theorem P_nonneg (x : ℝ) : 0 ≤ P x := by
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro t ht
  exact mul_nonneg ht.1 (Real.exp_pos _).le

end OAI.MetricKMedian.Analytic
end

section
namespace OAI.MetricKMedian.Analytic
theorem P_antitone : Antitone P := by
  intro x y hxy
  apply intervalIntegral.integral_mono_on (by norm_num) (texp_integrable y) (texp_integrable x)
  intro t ht
  apply mul_le_mul_of_nonneg_left _ ht.1
  apply Real.exp_le_exp.mpr
  nlinarith [ht.1]

end OAI.MetricKMedian.Analytic
end

section
namespace OAI.MetricKMedian.Analytic
theorem P_le_half {x : ℝ} (hx : 0 ≤ x) : P x ≤ 1 / 2 := by
  simpa using P_antitone hx

end OAI.MetricKMedian.Analytic
end

section
namespace OAI.MetricKMedian.Analytic
theorem A_le_one_add (x : ℝ) : A x ≤ 1 + x := by
  have hi : IntervalIntegrable (fun t : ℝ => 1 - Real.exp (-t * x))
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hi' : IntervalIntegrable (fun t : ℝ => t * x) MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
    (a := (0 : ℝ)) (b := 1) (by norm_num) hi hi' (fun t _ => by
      have he := Real.add_one_le_exp (-t * x)
      nlinarith)
  rw [intervalIntegral.integral_mul_const] at h
  norm_num at h
  unfold A
  simp only [neg_mul]
  linarith

end OAI.MetricKMedian.Analytic
end

section
namespace OAI.MetricKMedian.Analytic
theorem A_le_two {x : ℝ} (hx : x ≤ 1) : A x ≤ 2 := by
  linarith [A_le_one_add x]

end OAI.MetricKMedian.Analytic
end

section
namespace OAI.MetricKMedian.Analytic
theorem m_nonneg (x : ℝ) : 0 ≤ m x := by
  have h : 0 ≤ ∫ t : ℝ in 0..1,
      (1 - Real.exp (-t * x) - x * (t * Real.exp (-t * x))) := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro t _
    have he := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (t * x))
      (Real.exp_pos (-t * x)).le
    have hexp : Real.exp (t * x) * Real.exp (-t * x) = 1 := by
      rw [← Real.exp_add]
      convert Real.exp_zero using 2
      ring
    rw [hexp] at he
    nlinarith
  have hi : IntervalIntegrable (fun t : ℝ => 1 - Real.exp (-t * x))
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_sub hi ((texp_integrable x).const_mul x),
    intervalIntegral.integral_const_mul] at h
  unfold m A P
  linarith

end OAI.MetricKMedian.Analytic
end

section
namespace OAI.MetricKMedian.PhysicalPotential
open Analytic
variable {I : Type*}
theorem mass_nonneg {g : ℝ} (hg : 0 ≤ g) (S : Finset I) : 0 ≤ mass g S := by
  exact mul_nonneg hg (Nat.cast_nonneg _)

end OAI.MetricKMedian.PhysicalPotential
end

section
namespace OAI.MetricKMedian.PhysicalPotential
open Analytic
variable {I : Type*}
theorem cost_nonneg {g : ℝ} {d : I → ℝ} {S : Finset I} (hg : 0 ≤ g)
    (hd : ∀ i ∈ S, 0 ≤ d i) : 0 ≤ cost g d S := by
  exact Finset.sum_nonneg (fun i hi => mul_nonneg hg (hd i hi))

end OAI.MetricKMedian.PhysicalPotential
end

section
namespace OAI.MetricKMedian.PhysicalPotential
open Analytic
variable {I : Type*}
theorem mass_mono {g : ℝ} {S T : Finset I} (hg : 0 ≤ g) (hST : S ⊆ T) :
    mass g S ≤ mass g T := by
  apply mul_le_mul_of_nonneg_left _ hg
  exact_mod_cast Finset.card_le_card hST

end OAI.MetricKMedian.PhysicalPotential
end

section
namespace OAI.MetricKMedian.PhysicalPotential
open Analytic
variable {I : Type*}
theorem cost_mono {g : ℝ} {d : I → ℝ} {S T : Finset I} (hg : 0 ≤ g)
    (hd : ∀ i ∈ T, 0 ≤ d i) (hST : S ⊆ T) : cost g d S ≤ cost g d T := by
  exact Finset.sum_le_sum_of_subset_of_nonneg hST (fun i hi _ => mul_nonneg hg (hd i hi))

end OAI.MetricKMedian.PhysicalPotential
end

section
namespace OAI.MetricKMedian.PhysicalPotential
open Analytic
variable {I : Type*}
theorem B_nonneg (x : ℝ) : 0 ≤ B x := mul_nonneg (by norm_num) (P_nonneg x)

end OAI.MetricKMedian.PhysicalPotential
end

section
namespace OAI.MetricKMedian.PhysicalPotential
open Analytic
variable {I : Type*}
theorem retained_subset (a dh : ℝ) (d : I → ℝ) (T : Finset I) : retained a dh d T ⊆ T :=
  Finset.filter_subset _ _

end OAI.MetricKMedian.PhysicalPotential
end

section
namespace OAI.MetricKMedian.Analytic
open MeasureTheory Set Filter
open scoped Topology Filter Interval
theorem moment_integrable (n : ℕ) (x : ℝ) :
    IntervalIntegrable (fun t : ℝ => t^n*Real.exp (-t*x)) volume 0 1 := by
  apply Continuous.intervalIntegrable
  fun_prop

end OAI.MetricKMedian.Analytic
end

section
namespace OAI.MetricKMedian.Analytic
open MeasureTheory Set Filter
open scoped Topology Filter Interval
private theorem kernel_deriv (n : ℕ) (t x : ℝ) :
    HasDerivAt (fun z : ℝ => t^n*Real.exp (-t*z)) (-t^(n+1)*Real.exp (-t*x)) x := by
  have h := (((hasDerivAt_id x).const_mul (-t)).exp).const_mul (t^n)
  convert h using 1 <;> try rfl
  simp only [id_eq, mul_one, pow_succ]
  ring

end OAI.MetricKMedian.Analytic
end

section
namespace OAI.MetricKMedian.Analytic
open MeasureTheory Set Filter
open scoped Topology Filter Interval
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

end OAI.MetricKMedian.Analytic
end

section
namespace OAI.MetricKMedian.Analytic
open MeasureTheory Set Filter
open scoped Topology Filter Interval
theorem moment_nonneg (n : ℕ) (x : ℝ) : 0 ≤ moment n x := by
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro t ht
  exact mul_nonneg (pow_nonneg ht.1 n) (Real.exp_pos _).le

end OAI.MetricKMedian.Analytic
end

section
namespace OAI.MetricKMedian.Analytic
open MeasureTheory Set Filter
open scoped Topology Filter Interval
theorem moment_le_one (n : ℕ) {x : ℝ} (hx0 : 0 ≤ x) : moment n x ≤ 1 := by
  have h := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
    (moment_integrable n x) (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1:ℝ)) volume 0 1)
    (fun t (ht : t ∈ Icc (0:ℝ) 1) => show t^n*Real.exp (-t*x) ≤ (1:ℝ) from by
      have hpow : t^n ≤ 1 := pow_le_one₀ ht.1 ht.2
      have he : Real.exp (-t*x) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg ht.1 hx0])
      exact (mul_le_of_le_one_left (Real.exp_pos _).le hpow).trans he)
  simpa only [moment, intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_mul] using h

end OAI.MetricKMedian.Analytic
end

section
namespace OAI.MetricKMedian.Analytic
open MeasureTheory Set Filter
open scoped Topology Filter Interval
theorem P_eq_moment (x : ℝ) : P x = moment 1 x := by simp only [P, moment, pow_one]

end OAI.MetricKMedian.Analytic
end

section
namespace OAI.MetricKMedian.Analytic
open MeasureTheory Set Filter
open scoped Topology Filter Interval
theorem A_eq_moment (x : ℝ) : A x = 3-2*moment 0 x := by
  unfold A moment
  rw [intervalIntegral.integral_sub intervalIntegrable_const (by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [pow_zero, one_mul, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  ring

end OAI.MetricKMedian.Analytic
end

section
namespace OAI.MetricKMedian.Analytic
open MeasureTheory Set Filter
open scoped Topology Filter Interval
theorem hasDerivAt_A (x : ℝ) : HasDerivAt A (B x) x := by
  have h := ((hasDerivAt_moment 0 x).const_mul 2).const_sub 3
  have hd : HasDerivAt (fun z : ℝ => 3-2*moment 0 z) (B x) x := by
    refine h.congr_deriv ?_
    simp only [B, P_eq_moment, Nat.zero_add]
    ring
  exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall A_eq_moment)

end OAI.MetricKMedian.Analytic
end

section
namespace OAI.MetricKMedian.Analytic
open MeasureTheory Set Filter
open scoped Topology Filter Interval
theorem hasDerivAt_B (x : ℝ) : HasDerivAt B (-2*moment 2 x) x := by
  have h := (hasDerivAt_moment 1 x).const_mul 2
  have he : B = fun z => 2*moment 1 z := by funext z; simp only [B, P_eq_moment]
  rw [he]
  simpa only [neg_mul, mul_neg] using h

end OAI.MetricKMedian.Analytic
end

section
namespace OAI.MetricKMedian.Analytic
open MeasureTheory Set Filter
open scoped Topology Filter Interval
theorem coefficient_eq (x y : ℝ) : coefficient x y = 1+m x+B x*y := by
  unfold coefficient m B
  ring

end OAI.MetricKMedian.Analytic
end

section
namespace OAI.MetricKMedian.Analytic
open MeasureTheory Set Filter
open scoped Topology Filter Interval
theorem coefficient_ge_one {x y : ℝ} (hy : 0 ≤ y) : 1 ≤ coefficient x y := by
  rw [coefficient_eq]
  have hm := m_nonneg x
  have hB : 0 ≤ B x := mul_nonneg (by norm_num) (P_nonneg x)
  nlinarith only [hm, mul_nonneg hB hy]

end OAI.MetricKMedian.Analytic
end

section
namespace OAI.MetricKMedian.Analytic
open MeasureTheory Set Filter
open scoped Topology Filter Interval
theorem hasDerivAt_coefficient (x y : ℝ) :
    HasDerivAt (fun z => coefficient z y) (-2*(y-x)*moment 2 x) x := by
  have h := (hasDerivAt_A x).add ((hasDerivAt_B x).mul ((hasDerivAt_const x y).sub (hasDerivAt_id x)))
  change HasDerivAt (fun z => A z+B z*(y-z)) _ x
  convert h using 1 <;> try rfl
  dsimp only [id_eq, Pi.sub_apply]
  ring

end OAI.MetricKMedian.Analytic
end

section
namespace OAI.MetricKMedian.PhysicalPotential
open Analytic Finset
variable {I : Type*}
theorem B_le_one {x : ℝ} (hx : 0 ≤ x) : B x ≤ 1 := by
  have h := P_le_half hx
  unfold B
  linarith only [h]

end OAI.MetricKMedian.PhysicalPotential
end

section
namespace OAI.MetricKMedian.PhysicalPotential
open Analytic Finset
variable {I : Type*}
theorem m_le_one {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : m x ≤ 1 := by
  have hA := A_le_two hx1
  have hBx := mul_nonneg (B_nonneg x) hx0
  unfold m
  unfold B at hBx
  linarith only [hA, hBx]

end OAI.MetricKMedian.PhysicalPotential
end

section
namespace OAI.MetricKMedian.PhysicalPotential
open Analytic Finset
variable {I : Type*}
theorem coefficient_bounds {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : 1 ≤ coefficient x y ∧ coefficient x y ≤ 3 := by
  refine ⟨coefficient_ge_one hy0, ?_⟩
  rw [coefficient_eq]
  have hm := m_le_one hx0 hx1
  have hB := (mul_le_of_le_one_left hy0 (B_le_one hx0)).trans hy1
  linarith only [hm, hB]

end OAI.MetricKMedian.PhysicalPotential
end

section
namespace OAI.MetricKMedian.FixedBatch
open Finset PhysicalPotential Analytic
variable {I E : Type*} [DecidableEq I] [DecidableEq E] [Fintype E]
 theorem mem_relevant (D : Actions I E) (S : Finset I) (e : E) :
    e ∈ relevant D S ↔ (e ∈ D.ordinary ∧ D.source e ∈ S) ∨ (S ∩ D.erase e).Nonempty := by
  simp only [relevant, mem_filter, mem_univ, true_and]

end OAI.MetricKMedian.FixedBatch
end

section
namespace OAI.MetricKMedian.FixedBatch
open Finset PhysicalPotential Analytic
variable {I E : Type*} [DecidableEq I] [DecidableEq E] [Fintype E]
 theorem physical_subset (D : Actions I E) (S : Finset I) (A : Finset E) :
    physical D S A ⊆ S := sdiff_subset

end OAI.MetricKMedian.FixedBatch
end

section
namespace OAI.MetricKMedian.FixedBatch
open Finset PhysicalPotential Analytic
variable {I E : Type*} [DecidableEq I] [DecidableEq E] [Fintype E]
theorem physical_restrict (D : Actions I E) (S : Finset I) (A : Finset E) :
    physical D S A = physical D S (A ∩ relevant D S) := by
  ext i
  simp only [physical, mem_sdiff, mem_biUnion]
  constructor
  · rintro ⟨hi, hnot⟩
    refine ⟨hi, ?_⟩
    rintro ⟨e, he, hie⟩
    exact hnot ⟨e, (mem_inter.mp he).1, hie⟩
  · rintro ⟨hi, hnot⟩
    refine ⟨hi, ?_⟩
    rintro ⟨e, he, hie⟩
    have hrel : e ∈ relevant D S := (mem_relevant D S e).mpr (Or.inr ⟨i, mem_inter.mpr ⟨hi, hie⟩⟩)
    exact hnot ⟨e, mem_inter.mpr ⟨he, hrel⟩, hie⟩

end OAI.MetricKMedian.FixedBatch
end

section
namespace OAI.MetricKMedian.FixedBatch
open Finset PhysicalPotential Analytic
variable {I E : Type*} [DecidableEq I] [DecidableEq E] [Fintype E]
 theorem nextCap_le_force (D : Actions I E) (d : I → ℝ) (bForce : ℝ) (A : Finset E) :
    nextCap D d bForce A ≤ bForce := (fold_min_le _).mpr (Or.inl le_rfl)

end OAI.MetricKMedian.FixedBatch
end

section
namespace OAI.MetricKMedian.Analytic
open Set
 theorem hasDerivAt_timeRate (x y : ℝ) :
    HasDerivAt (fun z => timeRate z y) (rateDerivative x y) x := by
  have h := (((hasDerivAt_id x).const_mul 2).mul
    ((hasDerivAt_const x y).sub (hasDerivAt_id x))).mul (hasDerivAt_moment 2 x)
  convert h using 1 <;> try rfl
  dsimp only [rateDerivative, id_eq, Pi.sub_apply, Pi.mul_apply]
  norm_num only [Nat.reduceAdd]
  ring

end OAI.MetricKMedian.Analytic
end

section
namespace OAI.MetricKMedian.Analytic
open Set
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

end OAI.MetricKMedian.Analytic
end

section
namespace OAI.MetricKMedian.Analytic
open Set
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

end OAI.MetricKMedian.Analytic
end

section
namespace OAI.MetricKMedian.Analytic
open Set
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

end OAI.MetricKMedian.Analytic
end

section
namespace OAI.MetricKMedian.Analytic
open Set
 theorem hasDerivAt_phase (x t : ℝ) :
    HasDerivAt (fun u : ℝ => x*Real.exp (-u)) (-(x*Real.exp (-t))) t := by
  simpa only [neg_mul, mul_neg, mul_one, Pi.neg_apply, id_eq] using (((hasDerivAt_id t).neg).exp).const_mul x

end OAI.MetricKMedian.Analytic
end

section
namespace OAI.MetricKMedian.Analytic
open Set
 theorem phase_bounds {x t : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (ht : 0 ≤ t) :
    0 ≤ x*Real.exp (-t) ∧ x*Real.exp (-t) ≤ 1 := by
  refine ⟨mul_nonneg hx0 (Real.exp_pos _).le, ?_⟩
  exact (mul_le_of_le_one_left (Real.exp_pos _).le hx1).trans
    (Real.exp_le_one_iff.mpr (by linarith only [ht]))

end OAI.MetricKMedian.Analytic
end

section
namespace OAI.MetricKMedian.Analytic
open Set
 theorem hasDerivAt_timeCoefficient (x y t : ℝ) :
    HasDerivAt (fun u => coefficient (x*Real.exp (-u)) y)
      (timeRate (x*Real.exp (-t)) y) t := by
  have h := (hasDerivAt_coefficient (x*Real.exp (-t)) y).comp t (hasDerivAt_phase x t)
  convert h using 1 <;> try rfl
  dsimp only [timeRate]
  ring

end OAI.MetricKMedian.Analytic
end

section
namespace OAI.MetricKMedian.Analytic
open Set
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

end OAI.MetricKMedian.Analytic
end

section
namespace OAI.MetricKMedian.PhysicalPotential
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

end OAI.MetricKMedian.PhysicalPotential
end

section
namespace OAI.MetricKMedian.PhysicalPotential
open Analytic
variable {I : Type*}
theorem time_increase_le {x g h b : ℝ} {d : I → ℝ} {S : Finset I}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hg : 0 ≤ g) (hh : 0 ≤ h)
    (hd0 : ∀ i ∈ S, 0 ≤ d i) (hy : mass g S ≤ 1) :
    potential (x*Real.exp (-h)) g d S b-potential x g d S b ≤
      (2*h+6*h^2)*cost g d S := by
  have he := potential_time_error (b := b) hx0 hx1 hg hd0 hy hh
  have hr := (abs_le.mp (abs_timeRate hx0 hx1 (mass_nonneg hg S) hy)).2
  have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr hh) (cost_nonneg hg hd0)
  have ht := (le_abs_self _).trans he
  nlinarith only [ht, hm]

end OAI.MetricKMedian.PhysicalPotential
end

section
namespace OAI.MetricKMedian.FixedBatch
open Finset PhysicalPotential Analytic
variable {I E : Type*} [DecidableEq I] [DecidableEq E] [Fintype E]
 theorem nextAliveAt_subset (D : Actions I E) (a : ℝ) (d : I → ℝ)
    (S : Finset I) (A : Finset E) : nextAliveAt D a d S A ⊆ S := by
  unfold nextAliveAt
  split_ifs
  · exact (retained_subset _ _ _ _).trans (physical_subset D S A)
  · exact physical_subset D S A

end OAI.MetricKMedian.FixedBatch
end

section
namespace OAI.MetricKMedian.FixedBatch
open Finset PhysicalPotential Analytic
variable {I E : Type*} [DecidableEq I] [DecidableEq E] [Fintype E]
 theorem nextAliveAt_zero (D : Actions I E) (a : ℝ) (d : I → ℝ)
    (S : Finset I) (A : Finset E) (ha : A ∩ relevant D S=∅) :
    nextAliveAt D a d S A=S := by
  have hi : internal D S A=∅ := by simp only [internal, ha, filter_empty]
  simp only [nextAliveAt, hi, Finset.not_nonempty_empty, dite_false]
  rw [physical_restrict, ha]
  simp only [physical, biUnion_empty, sdiff_empty]

end OAI.MetricKMedian.FixedBatch
end

section
namespace OAI.MetricKMedian.FixedBatch
open Finset PhysicalPotential Analytic
variable {I E : Type*} [DecidableEq I] [DecidableEq E] [Fintype E]
 theorem changeAt_probability_le (D : Actions I E) (μ : FiniteLaw (Finset E))
    (a : ℝ) (d : I → ℝ) (S : Finset I) {Q : ℝ}
    (hmarg : ∀ e ∈ relevant D S, μ.prob (fun A => e ∈ A) ≤ Q) :
    μ.prob (fun A => nextAliveAt D a d S A ≠ S) ≤ ((relevant D S).card:ℝ)*Q := by
  have hm := μ.prob_mono (E := fun A => nextAliveAt D a d S A ≠ S)
    (F := fun A => ∃ e ∈ relevant D S, e ∈ A) (by
      intro A ha
      by_contra hn
      have hi : A ∩ relevant D S=∅ := eq_empty_iff_forall_notMem.mpr (by
        intro e he
        exact hn ⟨e, (mem_inter.mp he).2, (mem_inter.mp he).1⟩)
      exact ha (nextAliveAt_zero D a d S A hi))
  have hu := μ.prob_exists_le_sum (relevant D S) (fun e A => e ∈ A)
  have hs := sum_le_sum hmarg
  simp only [sum_const, nsmul_eq_mul] at hs
  exact hm.trans (hu.trans hs)

end OAI.MetricKMedian.FixedBatch
end

section
namespace OAI.MetricKMedian.FixedBatch
open Finset PhysicalPotential Analytic
variable {I E : Type*} [DecidableEq I] [DecidableEq E] [Fintype E]
theorem post_force_bound (D : Actions I E) (μ : FiniteLaw (Finset E))
    {x g h b V : ℝ} (a : ℝ) (d : I → ℝ) (S : Finset I)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hg0 : 0 < g) (hg1 : g ≤ 1)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hV : 0 ≤ V)
    (hd0 : ∀ i ∈ S, 0 ≤ d i) (hy : mass g S ≤ 1)
    (hVS : PhysicalPotential.cost g d S ≤ V) (hb0 : 0 ≤ b) (hbV : b ≤ V/g)
    (hcap : ∀ A, 0 ≤ nextCap D d b A)
    (hmarg : ∀ e ∈ relevant D S, μ.prob (fun A => e ∈ A) ≤ 2*h*g) :
    μ.expect (fun A => potential (x*Real.exp (-h)) g d (nextAliveAt D a d S A)
      (nextCap D d b A)-potential x g d S b) ≤
      (8*((relevant D S).card:ℝ)+8)*h*V := by
  let K : ℝ := (3+1/g)*V
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hpot0 : 0 ≤ potential x g d S b := by
    rw [potential, ← coefficient_eq]
    have ha := coefficient_ge_one (x := x) (mass_nonneg hg0.le S)
    exact add_nonneg (mul_nonneg (by linarith only [ha]) (cost_nonneg hg0.le hd0))
      (mul_nonneg (sub_nonneg.mpr hy) hb0)
  have hf : μ.expect (fun A => potential x g d (nextAliveAt D a d S A)
      (nextCap D d b A)-potential x g d S b) ≤
      K*μ.prob (fun A => nextAliveAt D a d S A ≠ S) := by
    rw [FiniteLaw.prob, ← μ.expect_mul]
    apply μ.expect_mono
    intro A
    have hsub := nextAliveAt_subset D a d S A
    have hnewV := (cost_mono hg0.le hd0 hsub).trans hVS
    have hy' := (mass_mono hg0.le hsub).trans hy
    by_cases heq : nextAliveAt D a d S A=S
    · simp only [heq, ne_eq, not_true_eq_false, ite_false, mul_zero]
      have he := mul_le_mul_of_nonneg_left (nextCap_le_force D d b A) (sub_nonneg.mpr hy)
      unfold potential
      linarith only [he]
    · simp only [heq, ne_eq, not_false_eq_true, ite_true, mul_one]
      have hcoeff := (coefficient_bounds hx0 hx1 (mass_nonneg hg0.le _) hy').2
      have hprod := mul_le_mul hcoeff hnewV
        (cost_nonneg hg0.le (fun i hi => hd0 i (hsub hi))) (by norm_num : (0:ℝ) ≤ 3)
      have hcapV := (nextCap_le_force D d b A).trans hbV
      have hcap' := mul_le_mul_of_nonneg_right
        (show 1-mass g (nextAliveAt D a d S A) ≤ 1 by
          linarith only [mass_nonneg hg0.le (nextAliveAt D a d S A)]) (hcap A)
      rw [potential, ← coefficient_eq]
      dsimp only [K]
      simp only [div_eq_mul_inv, one_mul] at hcapV ⊢
      nlinarith only [hprod, hcapV, hcap', hpot0]
  have hp := changeAt_probability_le D μ a d S hmarg
  have hf' := hf.trans (mul_le_mul_of_nonneg_left hp hK)
  have ht : μ.expect (fun A => potential (x*Real.exp (-h)) g d (nextAliveAt D a d S A)
      (nextCap D d b A)-potential x g d (nextAliveAt D a d S A) (nextCap D d b A)) ≤
      (2*h+6*h^2)*V := by
    apply (μ.expect_mono (fun A => ?_)).trans_eq (μ.expect_const _)
    have hsub := nextAliveAt_subset D a d S A
    exact (time_increase_le hx0 hx1 hg0.le hh0 (fun i hi => hd0 i (hsub hi))
      ((mass_mono hg0.le hsub).trans hy)).trans
      (mul_le_mul_of_nonneg_left ((cost_mono hg0.le hd0 hsub).trans hVS) (by positivity))
  have he : (fun A => potential (x*Real.exp (-h)) g d (nextAliveAt D a d S A)
      (nextCap D d b A)-potential x g d S b)=
      (fun A => (potential x g d (nextAliveAt D a d S A) (nextCap D d b A)-potential x g d S b)+
        (potential (x*Real.exp (-h)) g d (nextAliveAt D a d S A) (nextCap D d b A)-
          potential x g d (nextAliveAt D a d S A) (nextCap D d b A))) := by
    funext A; ring
  rw [he, μ.expect_add]
  apply (add_le_add hf' ht).trans
  have hk : K*(((relevant D S).card:ℝ)*(2*h*g)) ≤
      8*((relevant D S).card:ℝ)*h*V := by
    have hid : K*(((relevant D S).card:ℝ)*(2*h*g))=
        (6*g+2)*(((relevant D S).card:ℝ)*h*V) := by
      dsimp only [K]
      field_simp
      ring
    rw [hid]
    have hg' : 6*g+2 ≤ 8 := by linarith only [hg1]
    calc
      _ ≤ 8*(((relevant D S).card:ℝ)*h*V) := mul_le_mul_of_nonneg_right hg' (by positivity)
      _ = _ := by ring
  have ht' : (2*h+6*h^2)*V ≤ 8*h*V := by
    apply mul_le_mul_of_nonneg_right _ hV
    nlinarith only [mul_nonneg hh0 (sub_nonneg.mpr hh1)]
  nlinarith only [hk, ht']

end OAI.MetricKMedian.FixedBatch
end


open OAI OAI.MetricKMedian OAI.MetricKMedian.FixedBatch Finset OAI.MetricKMedian.PhysicalPotential OAI.MetricKMedian.Analytic in
theorem solution {I E : Type*} [DecidableEq I] [DecidableEq E] [Fintype E]
    (D : Actions I E) (μ : FiniteLaw (Finset E))
    {x g h b V : ℝ} (a : ℝ) (d : I → ℝ) (S : Finset I)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hg0 : 0 < g) (hg1 : g ≤ 1)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hV : 0 ≤ V)
    (hd0 : ∀ i ∈ S, 0 ≤ d i) (hy : mass g S ≤ 1)
    (hVS : PhysicalPotential.cost g d S ≤ V) (hb0 : 0 ≤ b) (hbV : b ≤ V/g)
    (hcap : ∀ A, 0 ≤ nextCap D d b A)
    (hmarg : ∀ e ∈ relevant D S, μ.prob (fun A => e ∈ A) ≤ 2*h*g) :
    μ.expect (fun A => potential (x*Real.exp (-h)) g d (nextAliveAt D a d S A)
      (nextCap D d b A)-potential x g d S b) ≤
      (8*((relevant D S).card:ℝ)+8)*h*V :=
  OAI.MetricKMedian.FixedBatch.post_force_bound D μ a d S hx0 hx1 hg0 hg1 hh0 hh1 hV hd0 hy hVS
    hb0 hbV hcap hmarg

end
