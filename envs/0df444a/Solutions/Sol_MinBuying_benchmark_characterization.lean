-- Prove2me | solution 1 for MinBuying.benchmark_characterization
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T17:08:12.802291+00:00
-- url     : https://prove2.me/submissions/55f6514e-7d3d-4ba6-a47d-0a51950d0727

import Theorems.Thm_MinBuying_budget_characterization

open Set MeasureTheory Filter
open scoped Interval Topology

noncomputable section

private lemma primitive_cont {g : ℝ → ℝ}
    (hg : ContinuousOn g (Ico (0 : ℝ) 1)) :
    ContinuousOn (fun x => ∫ t in (0 : ℝ)..x, g t) (Ico (0 : ℝ) 1) := by
  intro x hx
  let b := (x + 1) / 2
  have hxb : x < b := by dsimp [b]; linarith [hx.2]
  have hb0 : 0 ≤ b := le_trans hx.1 hxb.le
  have hb1 : b < 1 := by dsimp [b]; linarith [hx.2]
  have hg' : ContinuousOn g (Icc 0 b) := hg.mono (by
    intro t ht
    exact ⟨ht.1, lt_of_le_of_lt ht.2 hb1⟩)
  have hi : IntervalIntegrable g volume 0 b := hg'.intervalIntegrable_of_Icc hb0
  have hc : ContinuousOn (fun x => ∫ t in (0 : ℝ)..x, g t) (Icc 0 b) := by
    simpa only [uIcc_of_le hb0] using
      (intervalIntegral.continuousOn_primitive_interval' hi
        (left_mem_uIcc : (0 : ℝ) ∈ uIcc 0 b))
  apply (hc x ⟨hx.1, hxb.le⟩).mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hxb)] with t ht htb
  exact ⟨ht.1, htb.le⟩

private lemma primitive_deriv {g : ℝ → ℝ}
    (hg : ContinuousOn g (Ico (0 : ℝ) 1)) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun x => ∫ t in (0 : ℝ)..x, g t) (g x) x := by
  have hi : IntervalIntegrable g volume 0 x :=
    (hg.mono (show Icc (0 : ℝ) x ⊆ Ico 0 1 from fun _ ht =>
      ⟨ht.1, lt_of_le_of_lt ht.2 hx.2⟩)).intervalIntegrable_of_Icc hx.1.le
  have hm : StronglyMeasurableAtFilter g (𝓝 x) volume :=
    (hg.mono Ioo_subset_Ico_self).stronglyMeasurableAtFilter isOpen_Ioo x hx
  exact intervalIntegral.integral_hasDerivAt_right hi hm
    (hg.continuousAt (Ico_mem_nhds_iff.mpr hx))

open MinBuying

private lemma exponent_cont : ContinuousOn odeExponent (Ico (0 : ℝ) 1) :=
  primitive_cont (continuousOn_id.mul budget_characterization.2.1)

private lemma exponent_deriv {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt odeExponent (x * budgetSlope x) x :=
  primitive_deriv (continuousOn_id.mul budget_characterization.2.1) hx

private lemma integrand_cont : ContinuousOn
    (fun t => budgetSlope t * Real.exp (odeExponent t)) (Ico (0 : ℝ) 1) :=
  budget_characterization.2.1.mul exponent_cont.rexp

private lemma benchmark_cont : ContinuousOn continuousBenchmark (Ico (0 : ℝ) 1) :=
  exponent_cont.neg.rexp.mul (continuousOn_const.add (primitive_cont integrand_cont))

private lemma benchmark_deriv {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt continuousBenchmark
      (budgetSlope x * (1 - x * continuousBenchmark x)) x := by
  have hE := exponent_deriv hx
  have hJ := primitive_deriv integrand_cont hx
  have hd := hE.neg.exp.mul ((hasDerivAt_const x (1 : ℝ)).add hJ)
  convert! hd using 1
  try dsimp [continuousBenchmark]
  have he : Real.exp (-odeExponent x) * Real.exp (odeExponent x) = 1 := by
    rw [← Real.exp_add]
    simp
  nlinarith only [congrArg (fun t => budgetSlope x * t) he]

theorem solution :
    continuousBenchmark 0 = 1 ∧
    ContinuousOn continuousBenchmark (Ico (0 : ℝ) 1) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1,
      HasDerivAt continuousBenchmark
        (budgetSlope x * (1 - x * continuousBenchmark x)) x) ∧
    (∀ f : ℝ → ℝ, f 0 = 1 → ContinuousOn f (Ico (0 : ℝ) 1) →
      (∀ x ∈ Ioo (0 : ℝ) 1,
        HasDerivAt f (budgetSlope x * (1 - x * f x)) x) →
      EqOn f continuousBenchmark (Ico (0 : ℝ) 1)) := by
  refine ⟨by simp [continuousBenchmark, odeExponent], benchmark_cont,
    fun x hx => benchmark_deriv hx, ?_⟩
  intro f hf0 hfc hfd x hx
  have hsub : Icc (0 : ℝ) x ⊆ Ico 0 1 := fun _ ht =>
    ⟨ht.1, lt_of_le_of_lt ht.2 hx.2⟩
  have hc : ContinuousOn (fun t => Real.exp (odeExponent t) * f t) (Icc 0 x) :=
    (exponent_cont.rexp.mul hfc).mono hsub
  have hd : ∀ t ∈ Ioo (0 : ℝ) x,
      HasDerivAt (fun t => Real.exp (odeExponent t) * f t)
        (budgetSlope t * Real.exp (odeExponent t)) t := by
    intro t ht
    have ht' : t ∈ Ioo (0 : ℝ) 1 := ⟨ht.1, ht.2.trans hx.2⟩
    convert! (exponent_deriv ht').exp.mul (hfd t ht') using 1 <;> ring
  have hi : IntervalIntegrable
      (fun t => budgetSlope t * Real.exp (odeExponent t)) volume 0 x :=
    (integrand_cont.mono hsub).intervalIntegrable_of_Icc hx.1
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1 hc hd hi
  have hE0 : odeExponent 0 = 0 := by simp [odeExponent]
  simp only [hE0, Real.exp_zero, one_mul, hf0] at hFTC
  have he : Real.exp (-odeExponent x) * Real.exp (odeExponent x) = 1 := by
    rw [← Real.exp_add]
    simp
  dsimp [continuousBenchmark]
  rw [hFTC]
  calc
    f x = (Real.exp (-odeExponent x) * Real.exp (odeExponent x)) * f x := by
      rw [he, one_mul]
    _ = _ := by ring
