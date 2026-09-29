-- Prove2me | solution 1 for Hirsch.vertex_tight_rows_span
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T06:22:22.171546+00:00
-- url     : https://prove2.me/submissions/49cb9544-2551-4db6-b7b9-61d8ad49a133

import Mathlib
import Definitions.Def_Hirsch_model

set_option autoImplicit false
open scoped RealInnerProductSpace
open Filter Topology Hirsch

theorem solution (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (v : EuclideanSpace ℝ (Fin d)) (hv : v ∈ Set.extremePoints ℝ (Hpoly a b))
    (e : EuclideanSpace ℝ (Fin d)) (he : ∀ j, ⟪a j, v⟫ = b j → ⟪a j, e⟫ = 0) :
    e = 0 := by
  have hvP : ∀ j, ⟪a j, v⟫ ≤ b j := hv.1
  have hev : ∀ᶠ t : ℝ in 𝓝 0, v + t • e ∈ Hpoly a b := by
    change ∀ᶠ t : ℝ in 𝓝 0, ∀ j, ⟪a j, v + t • e⟫ ≤ b j
    apply Filter.eventually_all.mpr
    intro j
    by_cases hj : ⟪a j, v⟫ = b j
    · filter_upwards [] with t
      simp [inner_add_right, inner_smul_right, he j hj, hj]
    · have hlt : ⟪a j, v⟫ < b j := lt_of_le_of_ne (hvP j) hj
      have hc : Continuous (fun t : ℝ => ⟪a j, v + t • e⟫) := by fun_prop
      have hz : ⟪a j, v + (0 : ℝ) • e⟫ < b j := by simpa using hlt
      exact (hc.continuousAt.eventually (gt_mem_nhds hz)).mono fun _ h => le_of_lt h
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  have hhalf : 0 < δ / 2 := by linarith
  have hp : v + (δ / 2) • e ∈ Hpoly a b := by
    apply hball
    simp only [Real.dist_eq, sub_zero, abs_of_pos hhalf]
    linarith
  have hm0 : v + (-(δ / 2)) • e ∈ Hpoly a b := by
    apply hball
    simp only [Real.dist_eq, sub_zero, abs_neg, abs_of_pos hhalf]
    linarith
  have hm : v - (δ / 2) • e ∈ Hpoly a b := by
    simpa [neg_smul, sub_eq_add_neg] using hm0
  have hvEq : v + (δ / 2) • e = v :=
    hv.2 hp hm (mem_openSegment_add_sub (𝕜 := ℝ) v ((δ / 2) • e))
  have hs : (δ / 2) • e = 0 := by simpa using hvEq
  exact (smul_eq_zero.mp hs).resolve_left (ne_of_gt hhalf)

#print axioms solution
