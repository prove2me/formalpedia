-- Prove2me | solution 1 for KellyStochasticNetworks.wardrop_from_minimizer
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-26T22:37:21.054016+00:00
-- url     : https://prove2.me/submissions/79cc6834-ff9d-4740-a4b6-ae3d99dadb52

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop

namespace KellyStochasticNetworks

/-- For monotone continuous `D`, `∫_y^{y+h} D ≤ h · D(y+h)` for every real `h`. -/
lemma wm_int_le (D : ℝ → ℝ) (hD : Continuous D) (hmono : Monotone D) (y h : ℝ) :
    ∫ u in y..(y + h), D u ≤ h * D (y + h) := by
  rcases le_total 0 h with hh | hh
  · have hle : y ≤ y + h := by linarith
    have := intervalIntegral.integral_mono_on hle (hD.intervalIntegrable (μ := MeasureTheory.volume) y (y + h))
      (continuous_const.intervalIntegrable (μ := MeasureTheory.volume) y (y + h))
      (fun u hu => hmono hu.2 : ∀ u ∈ Set.Icc y (y + h), D u ≤ D (y + h))
    simp only [intervalIntegral.integral_const, smul_eq_mul] at this
    linarith
  · have hle : y + h ≤ y := by linarith
    have := intervalIntegral.integral_mono_on hle
      (continuous_const.intervalIntegrable (μ := MeasureTheory.volume) (y + h) y)
      (hD.intervalIntegrable (μ := MeasureTheory.volume) (y + h) y)
      (fun u hu => hmono hu.1 : ∀ u ∈ Set.Icc (y + h) y, D (y + h) ≤ D u)
    simp only [intervalIntegral.integral_const, smul_eq_mul] at this
    rw [intervalIntegral.integral_symm]
    linarith

theorem wm_main {J R Sd : ℕ} (A : Fin J → Fin R → ℝ) (s : Fin R → Fin Sd)
    (D : Fin J → ℝ → ℝ) (f : Fin Sd → ℝ)
    (hD : ∀ j, Continuous (D j)) (hmono : ∀ j, Monotone (D j))
    (x : Fin R → ℝ) (hx : x ∈ wardropFeasible s f)
    (hmin : ∀ z ∈ wardropFeasible s f, wardropObjective A D x ≤ wardropObjective A D z) :
    IsWardropEquilibrium A s D f x := by
  refine ⟨hx, fun r r' hs hxr => ?_⟩
  by_contra hlt
  push Not at hlt
  have hrr : r ≠ r' := by rintro rfl; exact lt_irrefl _ hlt
  set c : Fin J → ℝ := fun j => A j r' - A j r with hc
  set g : ℝ → ℝ := fun t => ∑ j, c j * D j (linkFlow A x j + t * c j) with hg
  have hg0 : g 0 < 0 := by
    have : g 0 = ∑ j, D j (linkFlow A x j) * A j r' - ∑ j, D j (linkFlow A x j) * A j r := by
      simp only [hg, hc, zero_mul, add_zero, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this]; linarith
  have hgc : Continuous g := by
    simp only [hg]
    exact continuous_finsetSum _ fun j _ =>
      continuous_const.mul ((hD j).comp (continuous_const.add (continuous_id.mul continuous_const)))
  have hev : ∀ᶠ t in nhds (0 : ℝ), g t < 0 := hgc.continuousAt.eventually_lt continuousAt_const hg0
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  set t := min (x r) (ε / 2) with ht
  have ht0 : 0 < t := lt_min hxr (by linarith)
  have htx : t ≤ x r := min_le_left _ _
  have hgt : g t < 0 := by
    apply hball
    rw [Real.dist_eq, sub_zero, abs_of_pos ht0]
    exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  -- the shifted flow
  set z : Fin R → ℝ := fun k => x k + t * ((if k = r' then 1 else 0) - (if k = r then 1 else 0))
    with hz
  have hzlink : ∀ j, linkFlow A z j = linkFlow A x j + t * c j := by
    intro j
    simp only [linkFlow, hz, hc, mul_add, Finset.sum_add_distrib]
    congr 1
    simp only [mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  have hzfeas : z ∈ wardropFeasible s f := by
    refine ⟨fun k => ?_, fun σ => ?_⟩
    · simp only [hz]
      by_cases hk : k = r
      · subst hk; simp [hrr]; linarith
      · have := hx.1 k
        simp only [hk, if_false, sub_zero]
        split_ifs <;> nlinarith
    · rw [← hx.2 σ]
      simp only [hz, Finset.sum_add_distrib, add_eq_left, ← Finset.mul_sum,
        Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hs]; simp
  have hobj : wardropObjective A D z - wardropObjective A D x ≤ t * g t := by
    simp only [wardropObjective, ← Finset.sum_sub_distrib, hg, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    rw [hzlink j, intervalIntegral.integral_interval_sub_left
      ((hD j).intervalIntegrable _ _) ((hD j).intervalIntegrable _ _)]
    have := wm_int_le (D j) (hD j) (hmono j) (linkFlow A x j) (t * c j)
    linarith
  have := hmin z hzfeas
  nlinarith

end KellyStochasticNetworks

open KellyStochasticNetworks

theorem solution {J R Sd : ℕ} (A : Fin J → Fin R → ℝ) (s : Fin R → Fin Sd)
    (D : Fin J → ℝ → ℝ) (f : Fin Sd → ℝ)
    (hA : ∀ j r, A j r = 0 ∨ A j r = 1)
    (hD : ∀ j, Continuous (D j)) (hmono : ∀ j, Monotone (D j))
    (x : Fin R → ℝ) (hx : x ∈ wardropFeasible s f)
    (hmin : ∀ z ∈ wardropFeasible s f, wardropObjective A D x ≤ wardropObjective A D z) :
    IsWardropEquilibrium A s D f x :=
  wm_main A s D f hD hmono x hx hmin
