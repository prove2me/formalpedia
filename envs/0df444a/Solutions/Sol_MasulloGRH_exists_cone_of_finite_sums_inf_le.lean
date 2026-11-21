-- Prove2me | solution 1 for MasulloGRH.exists_cone_of_finite_sums_inf_le
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-21T00:01:12.524546+00:00
-- url     : https://prove2.me/submissions/6cad9ce8-b03c-4f15-bc2f-5a2e30e25764

import Mathlib

set_option autoImplicit false

theorem solution (X ι : Type*) (S : Set X) (u : ι → X → ℝ)
    (hu : ∀ i, ∃ M : ℝ, ∀ t ∈ S, |u i t| ≤ M)
    (hsum : ∀ (n : ℕ) (i : Fin n → ι) (ε : ℝ), 0 < ε → ∃ t ∈ S, ∑ j, u (i j) t ≤ ε) :
    ∃ K : Set (X → ℝ), (∀ i, u i ∈ K) ∧ (∀ φ ∈ K, ∀ ψ ∈ K, φ + ψ ∈ K) ∧
      (∀ r : ℝ, 0 ≤ r → ∀ φ ∈ K, r • φ ∈ K) ∧
      (∀ φ ∈ K, ∃ M : ℝ, ∀ t ∈ S, |φ t| ≤ M) ∧
      (∀ φ ∈ K, ∀ ε : ℝ, 0 < ε → ∃ t ∈ S, φ t ≤ ε) := by
  classical
  choose M hM using hu
  have hlist : ∀ (L : List ι) (ε : ℝ), 0 < ε → ∃ t ∈ S, (L.map fun i => u i t).sum ≤ ε := by
    intro L ε hε
    obtain ⟨t, ht, h⟩ := hsum L.length L.get ε hε
    refine ⟨t, ht, ?_⟩
    have : ∑ j : Fin L.length, u (L.get j) t = (L.map fun i => u i t).sum := by
      rw [← List.sum_ofFn]
      congr 1
      apply List.ext_get <;> simp
    linarith
  obtain ⟨t0, ht0, -⟩ := hsum 0 Fin.elim0 1 one_pos
  have hM0 : ∀ i, 0 ≤ M i := fun i => (abs_nonneg _).trans (hM i t0 ht0)
  have key : ∀ (N : ℕ) (L : List (ℝ × ι)), (∀ p ∈ L, 0 ≤ p.1) → ∀ t ∈ S,
      (N : ℝ) * (L.map fun p => p.1 * u p.2 t).sum ≤
        ((L.flatMap fun p => List.replicate ⌈(N : ℝ) * p.1⌉₊ p.2).map fun i => u i t).sum
          + (L.map fun p => M p.2).sum := by
    intro N L hL t ht
    induction L with
    | nil => simp
    | cons p L ih =>
      have hp : 0 ≤ p.1 := hL p (by simp)
      have ih := ih (fun q hq => hL q (by simp [hq]))
      simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.map_append,
        List.sum_append, List.map_replicate, List.sum_replicate, nsmul_eq_mul]
      have h1 : (N : ℝ) * p.1 ≤ ⌈(N : ℝ) * p.1⌉₊ := Nat.le_ceil _
      have h2 : (⌈(N : ℝ) * p.1⌉₊ : ℝ) < N * p.1 + 1 :=
        Nat.ceil_lt_add_one (mul_nonneg (Nat.cast_nonneg _) hp)
      have hb := abs_le.1 (hM p.2 t ht)
      have hm := hM0 p.2
      nlinarith [mul_nonneg (sub_nonneg.2 h1) (by linarith : 0 ≤ u p.2 t + M p.2),
        mul_nonneg (by linarith : (0:ℝ) ≤ N * p.1 + 1 - ⌈(N : ℝ) * p.1⌉₊) hm]
  refine ⟨{φ | ∃ L : List (ℝ × ι), (∀ p ∈ L, 0 ≤ p.1) ∧
      ∀ t, φ t = (L.map fun p => p.1 * u p.2 t).sum}, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨[(1, i)], by simp, fun t => by simp⟩
  · rintro φ ⟨L1, h1, e1⟩ ψ ⟨L2, h2, e2⟩
    refine ⟨L1 ++ L2, ?_, fun t => ?_⟩
    · intro p hp
      rcases List.mem_append.1 hp with hp | hp
      exacts [h1 p hp, h2 p hp]
    · simp [e1, e2, List.sum_append]
  · rintro r hr φ ⟨L, h, e⟩
    refine ⟨L.map fun p => (r * p.1, p.2), ?_, fun t => ?_⟩
    · simp only [List.mem_map]
      rintro _ ⟨p, hp, rfl⟩
      exact mul_nonneg hr (h p hp)
    · simp only [Pi.smul_apply, smul_eq_mul, e, List.map_map, Function.comp_def,
        ← List.sum_map_mul_left, mul_assoc]
  · rintro φ ⟨L, -, e⟩
    refine ⟨(L.map fun p => |p.1| * M p.2).sum, fun t ht => ?_⟩
    rw [e]
    clear e
    induction L with
    | nil => simp
    | cons p L ih =>
      simp only [List.map_cons, List.sum_cons]
      calc |p.1 * u p.2 t + (L.map fun p => p.1 * u p.2 t).sum|
          ≤ |p.1 * u p.2 t| + |(L.map fun p => p.1 * u p.2 t).sum| := abs_add_le _ _
        _ ≤ _ := add_le_add (by
            rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hM _ t ht) (abs_nonneg _)) ih
  · rintro φ ⟨L, h, e⟩ ε hε
    have hB : 0 ≤ (L.map fun p => M p.2).sum :=
      List.sum_nonneg (by
        intro x hx
        obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx
        exact hM0 p.2)
    obtain ⟨N, hN⟩ := exists_nat_gt ((1 + (L.map fun p => M p.2).sum) / ε)
    obtain ⟨t, ht, hle⟩ := hlist (L.flatMap fun p => List.replicate ⌈(N : ℝ) * p.1⌉₊ p.2) 1 one_pos
    refine ⟨t, ht, ?_⟩
    have hk := key N L h t ht
    rw [← e t] at hk
    have hNe : 1 + (L.map fun p => M p.2).sum < N * ε := by
      rw [div_lt_iff₀ hε] at hN; exact hN
    have hNpos : (0 : ℝ) < N := by
      have : (0:ℝ) < (1 + (L.map fun p => M p.2).sum) / ε := div_pos (by linarith) hε
      linarith
    by_contra hc
    push Not at hc
    have := mul_lt_mul_of_pos_left hc hNpos
    linarith
