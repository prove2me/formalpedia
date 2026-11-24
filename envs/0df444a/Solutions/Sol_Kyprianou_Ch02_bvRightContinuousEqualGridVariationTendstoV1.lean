-- Prove2me | solution 1 for Kyprianou.Ch02.bvRightContinuousEqualGridVariationTendstoV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:39:08.731878+00:00
-- url     : https://prove2.me/submissions/c7b16ea8-e2a1-4927-855c-e390d8c193a0

import Theorems.Thm_Kyprianou_Ch02_variationOfMonotoneApproximantsTendstoV1
import Theorems.Thm_Kyprianou_Ch02_equalGridRightApproximantsV1
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (f : ℝ≥0 → ℝ) (a b : ℝ≥0) (hab : a ≤ b)
    (hBV : LocallyBoundedVariationOn f univ)
    (hr : ∀ t, ContinuousWithinAt f (Ici t) t) :
    let g : ℕ → ℕ → ℝ≥0 := fun n k =>
      a + (b - a) * (k : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)
    Tendsto (fun n => ∑ k ∈ Finset.range (n + 1), |f (g n (k+1)) - f (g n k)|)
      atTop (nhds (variationOnFromTo f univ a b)) := by
  dsimp only
  let g : ℕ → ℕ → ℝ≥0 := fun n k =>
    a + (b - a) * (k : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)
  obtain ⟨r, hm, hmem, himage, hright⟩ :=
    Kyprianou.Ch02.equalGridRightApproximantsV1 a b hab
  have hlim : ∀ x ∈ Icc a b,
      Tendsto (fun n => f (r n x)) atTop (nhds (f x)) :=
    fun x hx => (show Tendsto f (nhdsWithin x (Ici x)) (nhds (f x)) from hr x).comp (hright x hx)
  have h := Kyprianou.Ch02.variationOfMonotoneApproximantsTendstoV1
    f (Icc a b) r hm hmem hlim
  have hfin : eVariationOn f (Icc a b) ≠ ⊤ := by
    simpa only [BoundedVariationOn, univ_inter] using hBV a b (mem_univ a) (mem_univ b)
  have hreal := (ENNReal.tendsto_toReal hfin).comp h
  have hg (n : ℕ) : Monotone (g n) := by
    intro i j hij
    dsimp [g]
    gcongr
  have heq (n : ℕ) : (eVariationOn f (r n '' Icc a b)).toReal =
      ∑ k ∈ Finset.range (n+1), |f (g n (k+1)) - f (g n k)| := by
    rw [himage n, eVariationOn.image_range_of_monotone f (hg n)]
    rw [ENNReal.toReal_sum (fun _ _ => edist_ne_top _ _)]
    simp [edist_dist, Real.dist_eq, abs_sub_comm]
  simp only [Function.comp_def] at hreal
  simp_rw [heq] at hreal
  simpa [variationOnFromTo, hab, g] using hreal
