-- Prove2me | solution 1 for Kakutani1941.FixedPoint.enclosing_simplex
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T16:37:22.981615+00:00
-- url     : https://prove2.me/submissions/6cb8a443-2456-4657-b37f-5bbbbe05b408

import Mathlib

theorem solution {m : ℕ} {S : Set (EuclideanSpace ℝ (Fin m))}
    (hSbounded : Bornology.IsBounded S) :
    ∃ v : Fin (m + 1) → EuclideanSpace ℝ (Fin m),
      AffineIndependent ℝ v ∧ S ⊆ convexHull ℝ (Set.range v) := by
  classical
  obtain ⟨R0, hR0⟩ := hSbounded.exists_norm_le
  set R : ℝ := max R0 0 with hRdef
  have hR : 0 ≤ R := le_max_right _ _
  have hxR : ∀ x ∈ S, ∀ j, |x j| ≤ R := by
    intro x hx j
    have := PiLp.norm_apply_le x j
    rw [Real.norm_eq_abs] at this
    exact this.trans ((hR0 x hx).trans (le_max_left _ _))
  set N : ℝ := 2 * m * R + 1 with hN
  have hNpos : 0 < N := by positivity
  let c0 : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 (fun _ => -R)
  let v : Fin (m + 1) → EuclideanSpace ℝ (Fin m) :=
    Fin.cases c0 (fun j => c0 + N • EuclideanSpace.single j (1 : ℝ))
  refine ⟨v, ?_, ?_⟩
  · rw [affineIndependent_iff_linearIndependent_vsub ℝ v 0]
    have hli : LinearIndependent ℝ (fun j : Fin m => N • EuclideanSpace.single j (1 : ℝ)) :=
      (PiLp.linearIndependent_single_one 2 ℝ).units_smul (fun _ => Units.mk0 N hNpos.ne')
    let f : {x : Fin (m + 1) // x ≠ 0} → Fin m := fun i => i.1.pred i.2
    have hf : Function.Injective f := by
      intro i j h
      apply Subtype.ext
      simpa [f] using h
    have := hli.comp f hf
    have heq : (fun i : {x : Fin (m + 1) // x ≠ 0} => v i -ᵥ v 0) =
        (fun j : Fin m => N • EuclideanSpace.single j (1 : ℝ)) ∘ f := by
      funext i
      obtain ⟨i, hi⟩ := i
      obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.2 hi
      simp [v, f, vsub_eq_sub]
    rw [heq]; exact this
  · intro x hx
    let t : Fin m → ℝ := fun j => (x j + R) / N
    have ht0 : ∀ j, 0 ≤ t j := by
      intro j
      have := hxR x hx j
      exact div_nonneg (by linarith [neg_abs_le (x j)]) hNpos.le
    have htsum : ∑ j, t j ≤ 1 := by
      have : ∑ j, t j ≤ ∑ _j : Fin m, (2 * R) / N := by
        apply Finset.sum_le_sum
        intro j _
        have := hxR x hx j
        exact div_le_div_of_nonneg_right (by linarith [le_abs_self (x j)]) hNpos.le
      refine this.trans ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_div_assoc,
        div_le_one hNpos, hN]
      linarith
    let w : Fin (m + 1) → ℝ := Fin.cases (1 - ∑ j, t j) t
    have hw0 : ∀ i ∈ Finset.univ, 0 ≤ w i := by
      intro i _
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [w]; linarith
      · simpa [w] using ht0 j
    have hw1 : ∑ i, w i = 1 := by
      rw [Fin.sum_univ_succ]; simp [w]
    have hmem : ∀ i ∈ Finset.univ, v i ∈ convexHull ℝ (Set.range v) :=
      fun i _ => subset_convexHull ℝ _ ⟨i, rfl⟩
    have key := (convex_convexHull ℝ (Set.range v)).sum_mem hw0 hw1 hmem
    convert key using 1
    ext k
    rw [Fin.sum_univ_succ]
    simp only [w, v, Fin.cases_zero, Fin.cases_succ, smul_add, Finset.sum_add_distrib]
    simp only [PiLp.add_apply, PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply,
      EuclideanSpace.single_apply, smul_eq_mul]
    have hc0 : c0.ofLp k = -R := rfl
    have htk : t k * N = x k + R := by simp only [t]; field_simp
    simp only [hc0, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    rw [htk, ← Finset.sum_mul]
    ring
