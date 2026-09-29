-- Prove2me | solution 1 for Hirsch.relaxation_vertex
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T06:26:08.796968+00:00
-- url     : https://prove2.me/submissions/7f6d58d7-187c-4802-933c-f1b003baa33e

import Mathlib
import Definitions.Def_Hirsch_model

set_option autoImplicit false
open scoped RealInnerProductSpace
open Filter Topology Hirsch

lemma HirschSpanProof.span (d n : ℕ)
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



theorem solution (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (T : Finset (Fin n)) (Q : Set (EuclideanSpace ℝ (Fin d)))
    (hQ : ∀ z ∈ Q, ∀ j ∈ T, ⟪a j, z⟫ ≤ b j)
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ Set.extremePoints ℝ (Hpoly a b)) (hxQ : x ∈ Q)
    (hxT : ∀ j, ⟪a j, x⟫ = b j → j ∈ T) :
    x ∈ Set.extremePoints ℝ Q := by
  refine ⟨hxQ, ?_⟩
  intro y hy z hz hseg
  obtain ⟨r, s, hr, hs, hrs, hcomb⟩ := hseg
  have hspan : y - x = 0 := by
    apply HirschSpanProof.span d n a b x hx
    intro j hj
    have hjT := hxT j hj
    have hyj := hQ y hy j hjT
    have hzj := hQ z hz j hjT
    have hinner := congrArg (fun v => ⟪a j, v⟫) hcomb
    simp only [inner_add_right, inner_smul_right, hj] at hinner
    have hscale : r * b j + s * b j = b j := by
      calc
        r * b j + s * b j = (r+s) * b j := by ring
        _ = b j := by rw [hrs, one_mul]
    have hyEq : ⟪a j, y⟫ = b j := by
      by_contra hne
      have hlt : ⟪a j,y⟫ < b j := lt_of_le_of_ne hyj hne
      have hm := mul_lt_mul_of_pos_left hlt hr
      have hn := mul_le_mul_of_nonneg_left hzj (le_of_lt hs)
      linarith
    simp [inner_sub_right, hyEq, hj]
  exact sub_eq_zero.mp hspan

#print axioms solution
