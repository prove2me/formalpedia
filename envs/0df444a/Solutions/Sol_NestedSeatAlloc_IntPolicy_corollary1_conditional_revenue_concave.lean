-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.corollary1_conditional_revenue_concave
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T05:55:15.191006+00:00
-- url     : https://prove2.me/submissions/01aa15ff-fcb2-459c-9a3a-311d04c7a122

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_revenue_integrable
import Theorems.Thm_fare_abs_le_sum
import Theorems.Thm_fare_sum_nonneg
import Theorems.Thm_normalized_concave
import Theorems.Thm_concaveOn_add
import Theorems.Thm_concaveOn_mul_const
import Theorems.Thm_concave_min_clamped_of_monotone
import Theorems.Thm_condRevenue_three_branch
import Theorems.Thm_endpoint_secants_of_inSubdiff
import Theorems.Thm_normalized_mono_of_endpoint_secants
import Theorems.Thm_three_branch_eq_min_clamps

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ)
    (hM : IsSeatModel P X f) (hp : IsProtectionPolicy p)
    (k : ℕ) (hk : 1 ≤ k)
    (hconc : ConcaveOn ℝ (Set.Ici 0) (expRevenue P X f p k))
    (h14 : InSubdiff (expRevenue P X f p k) (p k) (f (k + 1)))
    (y : ℝ) (hy : 0 ≤ y) :
    ConcaveOn ℝ (Set.Ici 0) (condRevenue P X f p (k + 1) y) := by
  letI : IsProbabilityMeasure P := hM.isProb
  let g : ℝ → ℝ := expRevenue P X f p k
  let a : ℝ := p k
  let c : ℝ := f (k + 1)
  let h : ℝ → ℝ := fun t => g t - c * t
  have ha : 0 ≤ a := hp k hk
  let M : ℝ := ∑ i ∈ Finset.Icc 1 k, |f i|
  have hM0 : 0 ≤ M := fare_sum_nonneg f k
  have hfare : ∀ j, 1 ≤ j → j ≤ k → |f j| ≤ M := by
    intro j hj hjk
    exact fare_abs_le_sum f k j hj hjk
  have hXmeas : ∀ i, Measurable (X i) := hM.meas
  have hXnonneg : ∀ i ω, 0 ≤ X i ω := hM.nonneg
  have hbranch : ∀ s, 0 ≤ s →
      condRevenue P X f p (k + 1) y s =
        if s < a then g s else if s < a + y then
          (s - a) * c + g a else y * c + g (s - y) := by
    intro s hs
    have hIs := revenue_integrable P X hXmeas f p
      (fun j hj => hp j hj) hXnonneg M hM0 k hfare s hs
    have hIa := revenue_integrable P X hXmeas f p
      (fun j hj => hp j hj) hXnonneg M hM0 k hfare a ha
    have hIr : 0 ≤ s - y →
        Integrable (fun ω => revenue f p (fun i => X i ω) k (s - y)) P := by
      intro hsy
      exact revenue_integrable P X hXmeas f p
        (fun j hj => hp j hj) hXnonneg M hM0 k hfare (s - y) hsy
    simpa [g, a, c] using
      (condRevenue_three_branch P X f p k hk ha y s hy hIs hIa hIr)
  have hsub : InSubdiff g a c := by
    simpa [g, a, c] using h14
  have hsec := endpoint_secants_of_inSubdiff g a c ha hconc hsub
  have hmono := normalized_mono_of_endpoint_secants
    g a c ha hconc hsec.1 hsec.2
  have hhconc : ConcaveOn ℝ (Set.Ici 0) h :=
    normalized_concave g c hconc
  have hdecomp : ∀ t, g t = c * t + h t := by
    intro t
    simp [h]
  have hclamp := concave_min_clamped_of_monotone
    a y ha hy h hhconc hmono.1 hmono.2
  have hformula : ∀ s, 0 ≤ s →
      condRevenue P X f p (k + 1) y s =
        c * s + min (h (min s a)) (h (max (s - y) a)) := by
    intro s hs
    rw [hbranch s hs]
    exact three_branch_eq_min_clamps g h a c y s ha hy hs hdecomp hmono.1 hmono.2
  have hsum := concaveOn_add (concaveOn_mul_const c) hclamp
  exact hsum.congr (by
    intro s hs
    exact (hformula s hs).symm)
