-- Prove2me | solution 1 for GreedyRS.Greedy.lemma2_Cfun_strictAnti_continuous
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T10:37:10.483923+00:00
-- url     : https://prove2.me/submissions/a599769b-511f-4a1e-aefa-16cc0f38b469

import Mathlib
import Definitions.Def_GreedyRS_Greedy_Setting
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace G2C
open GreedyRS.Greedy

lemma Phi_mono : Monotone Phi := fun _ _ h => (cdf (gaussianReal 0 1)).mono h

lemma Phi_strictMono : StrictMono Phi := by
  intro a b hab
  have h1 : Phi b - Phi a = (gaussianReal 0 1).real (Set.Ioc a b) := by
    simp only [Phi, cdf_eq_real]
    have hI : Set.Ioc a b = Set.Iic b \ Set.Iic a := by
      ext x; simp only [Set.mem_Ioc, Set.mem_diff, Set.mem_Iic, not_le]; tauto
    rw [hI, measureReal_diff (Set.Iic_subset_Iic.2 hab.le) measurableSet_Iic]
  have h2 : 0 < (gaussianReal 0 1).real (Set.Ioc a b) := by
    have hv : (1 : ℝ≥0) ≠ 0 := one_ne_zero
    have hpos : (gaussianReal 0 1) (Set.Ioc a b) ≠ 0 := by
      intro h0
      have := gaussianReal_absolutelyContinuous' (0 : ℝ) hv h0
      simp [Real.volume_Ioc] at this
      linarith
    exact ENNReal.toReal_pos hpos (measure_ne_top _ _)
  linarith

lemma Phi_continuous : Continuous Phi := by
  set f := cdf (gaussianReal 0 1) with hf
  have hmono : Monotone f := f.mono
  rw [continuous_iff_continuousAt]
  intro a
  have hsing : f.measure {a} = 0 := by
    rw [hf, measure_cdf]
    have hv : (1 : ℝ≥0) ≠ 0 := one_ne_zero
    exact gaussianReal_absolutelyContinuous (0 : ℝ) hv (Real.volume_singleton)
  rw [StieltjesFunction.measure_singleton, ENNReal.ofReal_eq_zero] at hsing
  have hle : Function.leftLim f a ≤ f a := hmono.leftLim_le le_rfl
  have heq : Function.leftLim f a = f a := le_antisymm hle (by linarith)
  have hleft : ContinuousWithinAt f (Set.Iio a) a :=
    (hmono.continuousWithinAt_Iio_iff_leftLim_eq).2 heq
  have hright : ContinuousWithinAt f (Set.Ici a) a := f.right_continuous a
  exact continuousAt_iff_continuous_left'_right'.2 ⟨hleft, hright.mono Set.Ioi_subset_Ici_self⟩

lemma Phi_nonneg (t : ℝ) : 0 ≤ Phi t := cdf_nonneg _ _

lemma Phi_neg_le (s : ℝ) (hs : 0 ≤ s) : Phi (-s) ≤ Real.exp (-(s ^ 2) / 2) := by
  have hint : Integrable (fun x : ℝ => Real.exp (-s * id x)) (gaussianReal 0 1) := by
    exact integrable_exp_mul_gaussianReal (-s)
  have := measure_le_le_exp_mul_mgf (μ := gaussianReal 0 1) (X := id) (t := -s) (-s)
    (by linarith) hint
  rw [mgf_id_gaussianReal] at this
  simp only [Phi, cdf_eq_real]
  have hset : {ω : ℝ | id ω ≤ -s} = Set.Iic (-s) := by ext; simp
  rw [hset] at this
  refine this.trans (le_of_eq ?_)
  rw [← Real.exp_add]
  congr 1
  push_cast
  ring

/-- Uniform bound on the terms for `x ≥ θ > 0`. -/
lemma term_bound (θ x : ℝ) (hθ : 0 < θ) (hx : θ ≤ x) (n : ℕ) :
    ‖Phi (-(Real.sqrt ((n : ℝ) + 1)) * x) / ((n : ℝ) + 1)‖ ≤
      Real.exp (-(θ ^ 2) / 2) ^ (n + 1) := by
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hsq : 0 ≤ Real.sqrt ((n : ℝ) + 1) := Real.sqrt_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Phi_nonneg _) hn1.le)]
  have h1 : Phi (-(Real.sqrt ((n : ℝ) + 1)) * x) ≤ Phi (-(Real.sqrt ((n : ℝ) + 1) * θ)) := by
    apply Phi_mono
    nlinarith
  have h2 := Phi_neg_le (Real.sqrt ((n : ℝ) + 1) * θ) (by positivity)
  have h3 : Real.exp (-((Real.sqrt ((n : ℝ) + 1) * θ) ^ 2) / 2) =
      Real.exp (-(θ ^ 2) / 2) ^ (n + 1) := by
    rw [← Real.exp_nat_mul, mul_pow, Real.sq_sqrt hn1.le]
    congr 1; push_cast; ring
  calc Phi (-(Real.sqrt ((n : ℝ) + 1)) * x) / ((n : ℝ) + 1)
      ≤ Phi (-(Real.sqrt ((n : ℝ) + 1)) * x) :=
        div_le_self (Phi_nonneg _) (by linarith)
    _ ≤ _ := h1.trans (h2.trans h3.le)

lemma summable_geom (θ : ℝ) (hθ : 0 < θ) :
    Summable fun n : ℕ => Real.exp (-(θ ^ 2) / 2) ^ (n + 1) := by
  have hr : Real.exp (-(θ ^ 2) / 2) < 1 := by
    rw [Real.exp_lt_one_iff]; have := sq_pos_of_pos hθ; linarith
  have h := summable_geometric_of_lt_one (Real.exp_pos _).le hr
  exact (summable_nat_add_iff 1).2 h

lemma summable_terms (x : ℝ) (hx : 0 < x) :
    Summable fun n : ℕ => Phi (-(Real.sqrt ((n : ℝ) + 1)) * x) / ((n : ℝ) + 1) :=
  Summable.of_norm_bounded (summable_geom x hx) (fun n => term_bound x x hx le_rfl n)

theorem Cfun_strictAnti_continuous :
    StrictAntiOn Cfun (Set.Ioi 0) ∧ ContinuousOn Cfun (Set.Ioi 0) := by
  constructor
  · intro x hx y hy hxy
    simp only [Set.mem_Ioi] at hx hy
    unfold Cfun
    rw [Real.exp_lt_exp]
    refine Summable.tsum_lt_tsum (i := 0) ?_ ?_ (summable_terms y hy) (summable_terms x hx)
    · intro n
      have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hsq : 0 ≤ Real.sqrt ((n : ℝ) + 1) := Real.sqrt_nonneg _
      apply div_le_div_of_nonneg_right _ hn1.le
      apply Phi_mono
      nlinarith
    · simp only [CharP.cast_eq_zero, zero_add, Real.sqrt_one, neg_mul, one_mul, div_one]
      exact Phi_strictMono (by linarith)
  · intro x hx
    simp only [Set.mem_Ioi] at hx
    have hθ : 0 < x / 2 := by linarith
    have hcont : ContinuousOn (fun y => ∑' n : ℕ,
        Phi (-(Real.sqrt ((n : ℝ) + 1)) * y) / ((n : ℝ) + 1)) (Set.Ici (x / 2)) := by
      refine continuousOn_tsum (fun n => ?_) (summable_geom (x / 2) hθ) ?_
      · exact ((Phi_continuous.comp (continuous_const.mul continuous_id)).div_const _).continuousOn
      · intro n y hy
        exact term_bound (x / 2) y hθ hy n
    have hca : ContinuousAt (fun y => ∑' n : ℕ,
        Phi (-(Real.sqrt ((n : ℝ) + 1)) * y) / ((n : ℝ) + 1)) x :=
      hcont.continuousAt (Ici_mem_nhds (by linarith))
    exact (Real.continuous_exp.continuousAt.comp hca).continuousWithinAt

end G2C

theorem solution :
    StrictAntiOn GreedyRS.Greedy.Cfun (Set.Ioi 0) ∧ ContinuousOn GreedyRS.Greedy.Cfun (Set.Ioi 0) :=
  G2C.Cfun_strictAnti_continuous
