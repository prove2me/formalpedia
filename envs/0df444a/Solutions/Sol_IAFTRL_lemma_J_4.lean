-- Prove2me | solution 1 for IAFTRL.lemma_J_4
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-14T14:24:49.859208+00:00
-- url     : https://prove2.me/submissions/5200c258-765a-4297-82a7-7d27909b3534

import Definitions.Def_IAFTRL_chi

open MeasureTheory IAFTRL

private lemma chi_even (x : ℝ) : chi (-x) = chi x := by
  simp [chi, add_comm]

private lemma chi_abs (x : ℝ) : chi |x| = chi x := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_nonpos hx, chi_even]

private lemma chi_convex : ConvexOn ℝ Set.univ chi := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have hp := convexOn_exp.2 hx hy ha hb hab
  have hn := convexOn_exp.2 (Set.mem_univ (-x)) (Set.mem_univ (-y)) ha hb hab
  simp only [smul_eq_mul] at hp hn ⊢
  have hn' : Real.exp (-(a * x + b * y)) ≤ a * Real.exp (-x) + b * Real.exp (-y) := by
    simpa only [mul_neg, ← neg_add] using hn
  dsimp [chi]
  nlinarith

private lemma chi_nonneg (x : ℝ) : 0 ≤ chi x := by
  have h := Real.one_le_cosh x
  rw [Real.cosh_eq] at h
  dsimp [chi]
  linarith

private lemma chi_mono_abs (x y : ℝ) (h : |x| ≤ |y|) : chi x ≤ chi y := by
  have hc := Real.cosh_le_cosh.mpr h
  rw [Real.cosh_eq, Real.cosh_eq] at hc
  dsimp [chi]
  linarith

private lemma chi_exp_lower (x : ℝ) : Real.exp x - x - 1 ≤ chi x := by
  have h := Real.add_one_le_exp (-x)
  dsimp [chi]
  linarith

private lemma chi_global_bound (x : ℝ) : chi x ≤ x ^ 2 * Real.exp |x| := by
  have hmul : Real.exp |x| * Real.exp (-|x|) = 1 := by
    rw [← Real.exp_add]
    simp
  have hle : Real.exp (-|x|) ≤ 1 := by
    simpa using Real.exp_le_exp.mpr (neg_nonpos.mpr (abs_nonneg x))
  have ht : 1 - Real.exp (-|x|) ≤ |x| := by
    have h := Real.add_one_le_exp (-|x|)
    linarith
  have hs : (1 - Real.exp (-|x|)) ^ 2 ≤ |x| ^ 2 := by
    gcongr
  have heq : chi |x| = Real.exp |x| * (1 - Real.exp (-|x|)) ^ 2 := by
    dsimp [chi]
    calc
      Real.exp |x| + Real.exp (-|x|) - 2 =
          Real.exp |x| - 2 * (Real.exp |x| * Real.exp (-|x|)) +
            (Real.exp |x| * Real.exp (-|x|)) * Real.exp (-|x|) := by rw [hmul]; ring
      _ = _ := by ring
  rw [← chi_abs x, heq]
  calc
    _ ≤ Real.exp |x| * |x| ^ 2 := mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le
    _ = x ^ 2 * Real.exp |x| := by rw [sq_abs]; ring

private lemma chi_small_bound (x : ℝ) (hx : |x| ≤ 1) : chi x ≤ 3 / 2 * x ^ 2 := by
  have hp := (abs_le.mp (Real.exp_bound (n := 3) hx (by decide))).2
  have hn := (abs_le.mp (Real.exp_bound (n := 3) (x := -x) (by simpa) (by decide))).2
  norm_num [Finset.sum_range_succ, Nat.factorial] at hp hn
  have hc : |x| ^ 3 ≤ x ^ 2 := by
    calc
      |x| ^ 3 = |x| * x ^ 2 := by rw [pow_succ, sq_abs]; ring
      _ ≤ 1 * x ^ 2 := mul_le_mul_of_nonneg_right hx (sq_nonneg x)
      _ = _ := one_mul _
  dsimp [chi]
  nlinarith [sq_nonneg x]

private lemma bounded_integrable {X : Type*} [MeasurableSpace X]
    (q : Measure X) [IsProbabilityMeasure q] (f : X → ℝ)
    (hf : Measurable f) (M : ℝ) (hM : ∀ x, |f x| ≤ M) : Integrable f q := by
  refine (integrable_const M).mono' hf.aestronglyMeasurable (Filter.Eventually.of_forall ?_)
  intro x
  simpa only [Real.norm_eq_abs] using hM x

private lemma chi_integrable {X : Type*} [MeasurableSpace X]
    (q : Measure X) [IsProbabilityMeasure q] (f : X → ℝ)
    (hf : Measurable f) (M : ℝ) (hM : ∀ x, |f x| ≤ M) :
    Integrable (fun x => chi (f x)) q := by
  have hm : Measurable (fun x => chi (f x)) := by unfold chi; fun_prop
  refine (integrable_const (chi |M|)).mono' hm.aestronglyMeasurable
    (Filter.Eventually.of_forall ?_)
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (chi_nonneg _)]
  apply chi_mono_abs
  simpa only [abs_abs] using (hM x).trans (le_abs_self M)

private lemma chi_centered {X : Type*} [MeasurableSpace X]
    (q : Measure X) [IsProbabilityMeasure q] (f : X → ℝ)
    (hf : Measurable f) (hbound : ∃ M : ℝ, ∀ x, |f x| ≤ M) :
    ∫ x, chi (f x - ∫ y, f y ∂q) ∂q ≤ ∫ x, chi (2 * f x) ∂q := by
  obtain ⟨M, hM⟩ := hbound
  let m : ℝ := ∫ x, f x ∂q
  have htwo : ∀ x, |2 * f x| ≤ 2 * M := by
    intro x
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left (hM x) (by norm_num)
  have hcenter : ∀ x, |f x - m| ≤ M + |m| := by
    intro x
    exact (abs_sub (f x) m).trans (by linarith [hM x])
  have hi_two : Integrable (fun x => 2 * f x) q :=
    bounded_integrable q _ (hf.const_mul 2) _ htwo
  have hi_chi_two : Integrable (fun x => chi (2 * f x)) q :=
    chi_integrable q _ (hf.const_mul 2) _ htwo
  have hi_center : Integrable (fun x => chi (f x - m)) q :=
    chi_integrable q _ (hf.sub_const m) _ hcenter
  have hcont : Continuous chi := by unfold chi; fun_prop
  have hj := chi_convex.map_integral_le hcont.continuousOn isClosed_univ
    (Filter.Eventually.of_forall (fun x : X => Set.mem_univ (2 * f x))) hi_two hi_chi_two
  rw [integral_const_mul] at hj
  have hpoint : ∀ x, chi (f x - m) ≤ (1 / 2 : ℝ) * chi (2 * f x) +
      (1 / 2 : ℝ) * chi (2 * m) := by
    intro x
    have h := chi_convex.2 (Set.mem_univ (2 * f x)) (Set.mem_univ (-(2 * m)))
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
    simp only [smul_eq_mul, chi_even] at h
    convert h using 1 <;> congr 1 <;> ring
  have hint := integral_mono hi_center
    ((hi_chi_two.const_mul (1 / 2)).add (integrable_const ((1 / 2 : ℝ) * chi (2 * m)))) hpoint
  simp only [Pi.add_apply] at hint
  rw [integral_add (hi_chi_two.const_mul (1 / 2)) (integrable_const _),
    integral_const_mul, integral_const] at hint
  simp only [probReal_univ, one_smul] at hint
  change chi (2 * m) ≤ _ at hj
  change (∫ x, chi (f x - m) ∂q) ≤ _
  linarith

theorem solution :
    (∀ x : ℝ, chi (-x) = chi x) ∧ ConvexOn ℝ Set.univ chi ∧ (∀ x : ℝ, 0 ≤ chi x) ∧
    (∀ x y : ℝ, |x| ≤ |y| → chi x ≤ chi y) ∧
    (∀ x : ℝ, Real.exp x - x - 1 ≤ chi x) ∧ (∀ x : ℝ, chi x ≤ x ^ 2 * Real.exp |x|) ∧
    (∀ x : ℝ, |x| ≤ 1 → chi x ≤ 3 / 2 * x ^ 2) ∧
    (∀ {X : Type*} [MeasurableSpace X] (q : Measure X) [IsProbabilityMeasure q] (f : X → ℝ),
      Measurable f → (∃ M : ℝ, ∀ x, |f x| ≤ M) →
      ∫ x, chi (f x - ∫ y, f y ∂q) ∂q ≤ ∫ x, chi (2 * f x) ∂q) := by
  exact ⟨chi_even, chi_convex, chi_nonneg, chi_mono_abs, chi_exp_lower,
    chi_global_bound, chi_small_bound, chi_centered⟩
