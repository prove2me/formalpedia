-- Prove2me | solution 1 for MinBuying.continuous_dominates_step
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T17:12:23.30091+00:00
-- url     : https://prove2.me/submissions/233cde75-bd6b-48f4-bf85-f2d921229fa3

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

private lemma budget_cont : ContinuousOn canonicalBudget (Ico (0 : ℝ) 1) :=
  fun x hx => (budget_characterization.2.2.1 x hx).1.continuousWithinAt

private lemma budget_deriv {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt canonicalBudget (budgetSlope x) x :=
  (budget_characterization.2.2.1 x ⟨hx.1.le, hx.2⟩).1.hasDerivAt
    (Ico_mem_nhds_iff.mpr hx)

private def stepA (y t : ℝ) : ℝ :=
  Real.exp (canonicalBudget t - canonicalBudget y) - 1

private def stepD (y z t : ℝ) : ℝ := (stepA y t + z) / (1 + t * stepA y t)

private lemma stepA_nonneg {y t : ℝ} (hy : 0 ≤ y) (hyt : y ≤ t) (ht : t < 1) :
    0 ≤ stepA y t := by
  apply sub_nonneg.mpr
  apply Real.one_le_exp_iff.mpr
  exact sub_nonneg.mpr
    (budget_characterization.2.2.2.1.monotoneOn ⟨hy, hyt.trans_lt ht⟩
      ⟨hy.trans hyt, ht⟩ hyt)

private lemma step_den_pos {y t : ℝ} (hy : 0 ≤ y) (hyt : y ≤ t) (ht : t < 1) :
    0 < 1 + t * stepA y t := by
  have ha := stepA_nonneg hy hyt ht
  have ht0 := hy.trans hyt
  positivity

private lemma stepA_deriv {y t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (stepA y) (budgetSlope t * (1 + stepA y t)) t := by
  convert! ((budget_deriv ht).sub_const (canonicalBudget y)).exp.sub_const 1 using 1
  dsimp [stepA]
  ring

private lemma stepD_deriv {y z t : ℝ}
    (hy : 0 ≤ y) (hyt : y ≤ t) (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (stepD y z)
      ((budgetSlope t * (1 + stepA y t) * (1 - t * z) -
        stepA y t * (stepA y t + z)) / (1 + t * stepA y t) ^ 2) t := by
  have ha := stepA_deriv (y := y) ht
  have hn := ne_of_gt (step_den_pos hy hyt ht.2)
  convert! (ha.add_const z).div
    ((hasDerivAt_const t (1 : ℝ)).add ((hasDerivAt_id t).mul ha)) hn using 1
  dsimp only [Pi.add_apply, Pi.mul_apply, id_eq]
  field_simp [hn]
  ring

private lemma residual_identity (a s t z e : ℝ) (hn : 1 + t * a ≠ 0) :
    e * a / (1 + t * a) ^ 2 * (a + z - s * (1 - t) * (1 - t * z)) =
      s * e - (e * (t * s) * ((a + z) / (1 + t * a)) +
        e * ((s * (1 + a) * (1 - t * z) - a * (a + z)) / (1 + t * a) ^ 2)) := by
  have hn' : 1 + a * t ≠ 0 := by simpa only [mul_comm] using hn
  have hn2 : 1 + a * t * 2 + a ^ 2 * t ^ 2 ≠ 0 := by
    convert pow_ne_zero 2 hn' using 1 <;> ring
  field_simp [hn, hn', hn2]
  <;> ring

theorem solution (y z x : ℝ)
    (hy : 0 ≤ y) (hyx : y ≤ x) (hx : x < 1) (hz : 1 ≤ z) :
    let a := Real.exp (canonicalBudget x - canonicalBudget y) - 1
    (a + z) / (1 + x * a) ≤ benchmarkFlow y z x := by
  change stepD y z x ≤ benchmarkFlow y z x
  let J := fun t : ℝ => ∫ s in (0 : ℝ)..t, budgetSlope s * Real.exp (odeExponent s)
  let G := fun t : ℝ => J t - Real.exp (odeExponent t) * stepD y z t
  have hsub : Icc y x ⊆ Ico (0 : ℝ) 1 := fun _ ht =>
    ⟨hy.trans ht.1, ht.2.trans_lt hx⟩
  have haC : ContinuousOn (stepA y) (Icc y x) :=
    (((budget_cont.mono hsub).sub continuousOn_const).rexp).sub continuousOn_const
  have hdC : ContinuousOn (stepD y z) (Icc y x) :=
    (haC.add continuousOn_const).div
      (continuousOn_const.add (continuousOn_id.mul haC))
      (fun t ht => ne_of_gt (step_den_pos hy ht.1 (ht.2.trans_lt hx)))
  have hGC : ContinuousOn G (Icc y x) :=
    ((primitive_cont integrand_cont).mono hsub).sub
      ((exponent_cont.rexp.mono hsub).mul hdC)
  have hGD : ∀ t ∈ Ioo y x,
      HasDerivAt G
        (Real.exp (odeExponent t) * stepA y t / (1 + t * stepA y t) ^ 2 *
          (stepA y t + z - budgetSlope t * (1 - t) * (1 - t * z))) t := by
    intro t ht
    have ht' : t ∈ Ioo (0 : ℝ) 1 := ⟨hy.trans_lt ht.1, ht.2.trans hx⟩
    have hd := stepD_deriv (z := z) hy ht.1.le ht'
    have hn := ne_of_gt (step_den_pos hy ht.1.le ht'.2)
    convert! (primitive_deriv integrand_cont ht').sub
      ((exponent_deriv ht').exp.mul hd) using 1
    exact residual_identity (stepA y t) (budgetSlope t) t z (Real.exp (odeExponent t)) hn
  have hGN : ∀ t ∈ Ioo y x,
      0 ≤ Real.exp (odeExponent t) * stepA y t / (1 + t * stepA y t) ^ 2 *
        (stepA y t + z - budgetSlope t * (1 - t) * (1 - t * z)) := by
    intro t ht
    have ht' : t ∈ Ico (0 : ℝ) 1 := ⟨(hy.trans ht.1.le), ht.2.trans hx⟩
    have hs := (budget_characterization.2.2.1 t ht').2.1.le
    have hb := (budget_characterization.2.2.1 t ht').2.2
    have ha := stepA_nonneg hy ht.1.le ht'.2
    have hr : budgetSlope t * (1 - t) * (1 - t * z) ≤
        budgetSlope t * (1 - t) ^ 2 := by
      calc
        _ ≤ budgetSlope t * (1 - t) * (1 - t) :=
          mul_le_mul_of_nonneg_left (by nlinarith [ht'.1])
            (mul_nonneg hs (by linarith [ht'.2]))
        _ = _ := by ring
    have hres : 0 ≤ stepA y t + z - budgetSlope t * (1 - t) * (1 - t * z) := by
      linarith [ht'.1]
    exact mul_nonneg
      (div_nonneg (mul_nonneg (Real.exp_pos _).le ha) (sq_nonneg _)) hres
  have hmono : MonotoneOn G (Icc y x) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc y x) hGC
    · intro t ht
      have ht' : t ∈ Ioo y x := by simpa only [interior_Icc] using ht
      exact (hGD t ht').differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : t ∈ Ioo y x := by simpa only [interior_Icc] using ht
      rw [(hGD t ht').deriv]
      exact hGN t ht'
  have hm := hmono (left_mem_Icc.mpr hyx) (right_mem_Icc.mpr hyx) hyx
  have hsub0 : Icc (0 : ℝ) x ⊆ Ico 0 1 := fun _ ht => ⟨ht.1, ht.2.trans_lt hx⟩
  have hix : IntervalIntegrable
      (fun t => budgetSlope t * Real.exp (odeExponent t)) volume 0 x :=
    (integrand_cont.mono hsub0).intervalIntegrable_of_Icc (hy.trans hyx)
  have hiy : IntervalIntegrable
      (fun t => budgetSlope t * Real.exp (odeExponent t)) volume 0 y :=
    hix.mono_set (by simpa only [uIcc_of_le hy, uIcc_of_le (hy.trans hyx)] using
      (Icc_subset_Icc le_rfl hyx))
  have hiyx : IntervalIntegrable
      (fun t => budgetSlope t * Real.exp (odeExponent t)) volume y x :=
    (integrand_cont.mono hsub).intervalIntegrable_of_Icc hyx
  have hJ : (∫ t in y..x, budgetSlope t * Real.exp (odeExponent t)) = J x - J y := by
    have h := intervalIntegral.integral_add_adjacent_intervals hiy hiyx
    dsimp [J]
    linarith
  have hscale : (∫ t in y..x, budgetSlope t * Real.exp (odeExponent t - odeExponent y)) =
      Real.exp (-odeExponent y) * (J x - J y) := by
    have heq : (fun t => budgetSlope t * Real.exp (odeExponent t - odeExponent y)) =
        (fun t => Real.exp (-odeExponent y) * (budgetSlope t * Real.exp (odeExponent t))) := by
      funext t
      rw [sub_eq_add_neg, Real.exp_add]
      ring
    rw [heq, intervalIntegral.integral_const_mul, hJ]
  have hflow : Real.exp (odeExponent x) * benchmarkFlow y z x =
      Real.exp (odeExponent y) * z + (J x - J y) := by
    rw [benchmarkFlow, hscale]
    simp only [Real.exp_neg, Real.exp_sub]
    field_simp
    <;> ring
  apply (mul_le_mul_iff_right₀ (Real.exp_pos (odeExponent x))).mp
  rw [hflow]
  have hyD : stepD y z y = z := by simp [stepD, stepA]
  dsimp only [G] at hm
  rw [hyD] at hm
  linarith

