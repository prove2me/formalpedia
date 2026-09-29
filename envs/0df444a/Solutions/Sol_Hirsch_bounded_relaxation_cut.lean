-- Prove2me | solution 1 for Hirsch.bounded_relaxation_cut
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T06:33:40.786159+00:00
-- url     : https://prove2.me/submissions/382d25aa-264c-461b-98fb-572fa6173036

import Mathlib
import Definitions.Def_Hirsch_model

set_option autoImplicit false
open scoped RealInnerProductSpace
open Filter Topology Hirsch

theorem HirschCutProof.span (d n : ℕ)
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
    (hbd : Bornology.IsBounded (Hpoly a b)) (T : Finset (Fin n))
    (v : EuclideanSpace ℝ (Fin d)) (hv : v ∈ Set.extremePoints ℝ (Hpoly a b))
    (hvT : ∀ j, ⟪a j, v⟫ = b j → j ∈ T) :
    ∃ M : ℝ, (∀ x ∈ Hpoly a b, ⟪-∑ j ∈ T, a j, x⟫ ≤ M) ∧
      Bornology.IsBounded {x : EuclideanSpace ℝ (Fin d) |
        (∀ j ∈ T, ⟪a j, x⟫ ≤ b j) ∧ ⟪-∑ j ∈ T, a j, x⟫ ≤ M} := by
  classical
  obtain ⟨R, hR⟩ := hbd.exists_norm_le
  let M : ℝ := ‖-∑ j ∈ T, a j‖ * R
  have hM : ∀ x ∈ Hpoly a b, ⟪-∑ j ∈ T, a j, x⟫ ≤ M := by
    intro x hx
    exact (real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (hR x hx) (norm_nonneg _))
  refine ⟨M, hM, ?_⟩
  let L : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := fun x j => if j ∈ T then ⟪a j, x⟫ else 0
      map_add' := by
        intro x y
        ext j
        by_cases hj : j ∈ T <;> simp [hj, inner_add_right]
      map_smul' := by
        intro c x
        ext j
        by_cases hj : j ∈ T <;> simp [hj, inner_smul_right] }
  have hLi : Function.Injective L := by
    intro x y hxy
    have hz : x - y = 0 := by
      apply HirschCutProof.span d n a b v hv
      intro j hj
      have heq := congrFun hxy j
      have hjT := hvT j hj
      simpa [L, hjT, inner_sub_right] using sub_eq_zero.mpr heq
    exact sub_eq_zero.mp hz
  obtain ⟨K, _, hK⟩ := L.injective_iff_antilipschitz.mp hLi
  let lo : Fin n → ℝ := fun j => if j ∈ T then -M - ∑ k ∈ T.erase j, b k else 0
  let hi : Fin n → ℝ := fun j => if j ∈ T then b j else 0
  have hbox : Bornology.IsBounded (Set.pi Set.univ fun j => Set.Icc (lo j) (hi j)) :=
    Bornology.IsBounded.pi fun j => Metric.isBounded_Icc _ _
  apply (hK.isBounded_preimage hbox).subset
  intro x hx
  change ∀ j ∈ Set.univ, L x j ∈ Set.Icc (lo j) (hi j)
  intro j _
  by_cases hj : j ∈ T
  · have hsum : ∑ k ∈ T.erase j, ⟪a k, x⟫ ≤ ∑ k ∈ T.erase j, b k :=
      Finset.sum_le_sum fun k hk => hx.1 k (Finset.mem_of_mem_erase hk)
    have htotal : -(∑ k ∈ T, ⟪a k, x⟫) ≤ M := by
      simpa only [inner_neg_left, sum_inner] using hx.2
    have hsplit := Finset.sum_erase_add T (fun k => ⟪a k, x⟫) hj
    change (if j ∈ T then -M - ∑ k ∈ T.erase j, b k else 0) ≤
      (if j ∈ T then ⟪a j, x⟫ else 0) ∧
      (if j ∈ T then ⟪a j, x⟫ else 0) ≤ (if j ∈ T then b j else 0)
    simp only [if_pos hj]
    exact ⟨by linarith, hx.1 j hj⟩
  · simp [L, lo, hi, hj]

#print axioms solution
