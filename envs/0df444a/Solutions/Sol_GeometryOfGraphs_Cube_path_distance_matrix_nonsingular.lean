-- Prove2me | solution 1 for GeometryOfGraphs.Cube.path_distance_matrix_nonsingular
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T21:11:23.835661+00:00
-- url     : https://prove2.me/submissions/93b893e4-e89a-4d17-a13c-0c5c7ac56ce4

import Mathlib
set_option autoImplicit false
open scoped BigOperators

private lemma abs_second (i j : ℕ) (hi : 1 ≤ i) :
    |((i-1 : ℕ) : ℝ) - (j : ℝ)| - 2 * |(i : ℝ) - (j : ℝ)| +
      |((i+1 : ℕ) : ℝ) - (j : ℝ)| = if i = j then 2 else 0 := by
  have hcast : ((i-1 : ℕ) : ℝ) = (i : ℝ) - 1 := by
    rw [Nat.cast_sub hi]; norm_num
  rw [hcast, Nat.cast_add, Nat.cast_one]
  by_cases h : i = j
  · subst j; simp; norm_num
  · by_cases hij : i < j
    · have hh : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hij
      rw [if_neg h, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith),
        abs_of_nonpos (by linarith)]
      ring
    · have hh : (j : ℝ) ≤ (i : ℝ) - 1 := by
        have : j ≤ i-1 := by omega
        exact_mod_cast this
      rw [if_neg h, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith),
        abs_of_nonneg (by linarith)]
      ring

theorem solution (m : ℕ) (hm : 2 ≤ m) :
    (Matrix.of (fun r s : Fin m =>
      |((r : ℕ) : ℝ) - ((s : ℕ) : ℝ)|)).det ≠ 0 := by
  classical
  let A : Matrix (Fin m) (Fin m) ℝ := Matrix.of (fun r s =>
    |((r : ℕ) : ℝ) - ((s : ℕ) : ℝ)|)
  have hker : ∀ v : Fin m → ℝ, A.mulVec v = 0 → v = 0 := by
    intro v hv
    have hrow (i : Fin m) : ∑ j : Fin m, |(i.val : ℝ) - (j.val : ℝ)| * v j = 0 := by
      exact congrFun hv i
    have hint (i : Fin m) (hi : 1 ≤ i.val) (hit : i.val+1 < m) : v i = 0 := by
      have h₁ := hrow ⟨i.val-1, by omega⟩
      have h₂ := hrow i
      have h₃ := hrow ⟨i.val+1, hit⟩
      have he : ∑ j : Fin m,
          (|((i.val-1 : ℕ) : ℝ) - (j.val : ℝ)| -
            2 * |(i.val : ℝ) - (j.val : ℝ)| +
            |((i.val+1 : ℕ) : ℝ) - (j.val : ℝ)|) * v j = 2 * v i := by
        simp_rw [abs_second _ _ hi]
        simp_rw [← Fin.ext_iff]
        simp
      have hz : ∑ j : Fin m,
          (|((i.val-1 : ℕ) : ℝ) - (j.val : ℝ)| -
            2 * |(i.val : ℝ) - (j.val : ℝ)| +
            |((i.val+1 : ℕ) : ℝ) - (j.val : ℝ)|) * v j = 0 := by
        simp_rw [add_mul, sub_mul, mul_assoc]
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, h₁, h₂, h₃]
        ring
      linarith
    let first : Fin m := ⟨0, by omega⟩
    let last : Fin m := ⟨m-1, by omega⟩
    have hfirst : v first = 0 := by
      have hh := hrow last
      have he : (∑ j : Fin m, |(last.val : ℝ) - (j.val : ℝ)| * v j) =
          |(last.val : ℝ) - (first.val : ℝ)| * v first := by
        apply Finset.sum_eq_single first
        · intro j hj hne
          by_cases hjl : j = last
          · subst j; simp
          · have hj0 : 1 ≤ j.val := by
              have : j.val ≠ 0 := by intro h; apply hne; apply Fin.ext; exact h
              omega
            have hjt : j.val+1 < m := by
              have : j.val ≠ m-1 := by intro h; apply hjl; apply Fin.ext; exact h
              omega
            rw [hint j hj0 hjt, mul_zero]
        · simp
      rw [he] at hh
      have hpos : 0 < |(last.val : ℝ) - (first.val : ℝ)| := by
        dsimp [last, first]
        have : 0 < (m-1 : ℕ) := by omega
        rw [Nat.cast_zero, sub_zero, abs_of_nonneg (Nat.cast_nonneg (m-1) : (0 : ℝ) ≤ ↑(m-1))]
        exact_mod_cast this
      exact (mul_eq_zero.mp hh).resolve_left hpos.ne'
    have hlast : v last = 0 := by
      have hh := hrow first
      have he : (∑ j : Fin m, |(first.val : ℝ) - (j.val : ℝ)| * v j) =
          |(first.val : ℝ) - (last.val : ℝ)| * v last := by
        apply Finset.sum_eq_single last
        · intro j hj hne
          by_cases hjf : j = first
          · subst j; rw [hfirst, mul_zero]
          · have hj0 : 1 ≤ j.val := by
              have : j.val ≠ 0 := by intro h; apply hjf; apply Fin.ext; exact h
              omega
            have hjt : j.val+1 < m := by
              have : j.val ≠ m-1 := by intro h; apply hne; apply Fin.ext; exact h
              omega
            rw [hint j hj0 hjt, mul_zero]
        · simp
      rw [he] at hh
      have hpos : 0 < |(first.val : ℝ) - (last.val : ℝ)| := by
        rw [abs_sub_comm]
        dsimp [last, first]
        have : 0 < (m-1 : ℕ) := by omega
        rw [Nat.cast_zero, sub_zero, abs_of_nonneg (Nat.cast_nonneg (m-1) : (0 : ℝ) ≤ ↑(m-1))]
        exact_mod_cast this
      exact (mul_eq_zero.mp hh).resolve_left hpos.ne'
    funext i
    by_cases hf : i = first
    · subst i; exact hfirst
    by_cases hl : i = last
    · subst i; exact hlast
    have hi0 : 1 ≤ i.val := by
      have : i.val ≠ 0 := by intro h; apply hf; apply Fin.ext; exact h
      omega
    have hit : i.val+1 < m := by
      have : i.val ≠ m-1 := by intro h; apply hl; apply Fin.ext; exact h
      omega
    exact hint i hi0 hit
  have hinj : Function.Injective A.mulVec := by
    intro v w h
    have hh : A.mulVec (v-w) = 0 := by rw [Matrix.mulVec_sub, h, sub_self]
    have := hker (v-w) hh
    exact sub_eq_zero.mp this
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det A).mp (Matrix.mulVec_injective_iff_isUnit.mp hinj))

#print axioms solution
