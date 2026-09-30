-- Prove2me | solution 1 for KellyStochasticNetworks.primal_utility_strictConcave
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T01:24:30.347133+00:00
-- url     : https://prove2.me/submissions/3f134dae-dbde-41ea-909b-8ff993ef5797

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_KellyStochasticNetworks_Congestion

namespace KellyStochasticNetworks

lemma pr_P_convex (q : ℝ → ℝ) (hq : Continuous q) (hmono : Monotone q) :
    ConvexOn ℝ Set.univ (fun u => ∫ s in (0:ℝ)..u, q s) := by
  have hd : ∀ u, HasDerivAt (fun u => ∫ s in (0:ℝ)..u, q s) (q u) u :=
    fun u => (hq.integral_hasStrictDerivAt 0 u).hasDerivAt
  have hderiv : deriv (fun u => ∫ s in (0:ℝ)..u, q s) = q := funext fun u => (hd u).deriv
  refine Monotone.convexOn_univ_of_deriv (fun u => (hd u).differentiableAt) ?_
  rw [hderiv]; exact hmono

theorem pr_strictConcave {J R : ℕ} (A : Fin J → Fin R → ℝ) (w : Fin R → ℝ)
    (p : Fin J → ℝ → ℝ) (hw : ∀ r, 0 < w r)
    (hp : ∀ j, Continuous (p j)) (hpmono : ∀ j, Monotone (p j)) :
    StrictConcaveOn ℝ {x : Fin R → ℝ | ∀ r, 0 < x r} (primalUtility A w p) := by
  have hconv : Convex ℝ {x : Fin R → ℝ | ∀ r, 0 < x r} := by
    intro x hx y hy a b ha hb hab r
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases ha.eq_or_lt with rfl | ha'
    · rw [zero_add] at hab; subst hab
      have := hy r; simp only [zero_mul, zero_add, one_mul]; exact this
    · have := mul_pos ha' (hx r); have := mul_nonneg hb (hy r).le; linarith
  refine ⟨hconv, fun x hx y hy hxy a b ha hb hab => ?_⟩
  obtain ⟨r0, hr0⟩ := Function.ne_iff.mp hxy
  have hP := fun j => pr_P_convex (p j) (hp j) (hpmono j)
  unfold primalUtility
  simp only [smul_eq_mul]
  have h1 : a * ∑ r, w r * Real.log (x r) + b * ∑ r, w r * Real.log (y r) <
      ∑ r, w r * Real.log ((a • x + b • y) r) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_lt_sum
    · intro r _
      have := strictConcaveOn_log_Ioi.concaveOn.2 (hx r) (hy r) ha.le hb.le hab
      simp only [smul_eq_mul] at this
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have m := mul_le_mul_of_nonneg_left this (hw r).le
      have e : w r * (a * Real.log (x r) + b * Real.log (y r)) =
          a * (w r * Real.log (x r)) + b * (w r * Real.log (y r)) := by ring
      linarith
    · refine ⟨r0, Finset.mem_univ _, ?_⟩
      have := strictConcaveOn_log_Ioi.2 (hx r0) (hy r0) hr0 ha hb hab
      simp only [smul_eq_mul] at this
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have m := mul_lt_mul_of_pos_left this (hw r0)
      have e : w r0 * (a * Real.log (x r0) + b * Real.log (y r0)) =
          a * (w r0 * Real.log (x r0)) + b * (w r0 * Real.log (y r0)) := by ring
      linarith
  have h2 : (∑ j, (∫ s in (0:ℝ)..(linkFlow A (a • x + b • y) j), p j s)) ≤
      a * (∑ j, (∫ s in (0:ℝ)..(linkFlow A x j), p j s)) +
        b * (∑ j, (∫ s in (0:ℝ)..(linkFlow A y j), p j s)) := by
    have e : a * (∑ j, (∫ s in (0:ℝ)..(linkFlow A x j), p j s)) +
        b * (∑ j, (∫ s in (0:ℝ)..(linkFlow A y j), p j s)) =
        ∑ j, (a * (∫ s in (0:ℝ)..(linkFlow A x j), p j s) +
          b * (∫ s in (0:ℝ)..(linkFlow A y j), p j s)) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    rw [e]
    refine Finset.sum_le_sum fun j _ => ?_
    have hL : linkFlow A (a • x + b • y) j = a * linkFlow A x j + b * linkFlow A y j := by
      simp only [linkFlow, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun r _ => by ring
    rw [hL]
    have := (hP j).2 (Set.mem_univ (linkFlow A x j)) (Set.mem_univ (linkFlow A y j)) ha.le hb.le hab
    simpa only [smul_eq_mul] using this
  linarith

end KellyStochasticNetworks

open KellyStochasticNetworks

theorem solution {J R : ℕ} (A : Fin J → Fin R → ℝ) (w : Fin R → ℝ)
    (p : Fin J → ℝ → ℝ) (hA : ∀ j r, 0 ≤ A j r) (hw : ∀ r, 0 < w r)
    (hp : ∀ j, Continuous (p j)) (hpmono : ∀ j, Monotone (p j)) (hpnn : ∀ j y, 0 ≤ p j y) :
    StrictConcaveOn ℝ {x : Fin R → ℝ | ∀ r, 0 < x r} (primalUtility A w p) := by
  exact pr_strictConcave A w p hw hp hpmono
