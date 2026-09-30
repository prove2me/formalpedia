-- Prove2me | solution 1 for Komlos.beck_fiala_banaszczyk
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T02:47:22.164196+00:00
-- url     : https://prove2.me/submissions/088dea11-b7a6-48c1-b31e-5707b636ca94
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Komlos_model
import Theorems.Thm_Komlos_banaszczyk_bound

open Komlos

/-- Column scaling: a uniform `ℓ∞` bound `B` for signed sums of unit-norm vector families in
`ℝ^m` (with `n` vectors) transfers to degree-`t` zero-one matrices with the factor `√t`. -/
private lemma scaling_transfer (B : ℝ) (t n m : ℕ) (A : Fin m → Fin n → ℝ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hdeg : ∀ j, ({i | A i j = 1} : Finset (Fin m)).card ≤ t)
    (hB : ∀ v : Fin n → EuclideanSpace ℝ (Fin m), (∀ i, ‖v i‖ ≤ 1) →
      ∃ ε : Fin n → ℝ, IsSignVector ε ∧ ∀ j, |∑ i, ε i * v i j| ≤ B) :
    ∃ ε : Fin n → ℝ, IsSignVector ε ∧
      ∀ i, |∑ j, A i j * ε j| ≤ B * Real.sqrt t := by
  have hcol : ∀ j, ∑ i, A i j ^ 2 ≤ (t : ℝ) := by
    intro j
    have h1 : ∑ i, A i j ^ 2 = ∑ i, (if A i j = 1 then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      rcases h01 i j with h | h <;> simp [h]
    rw [h1, Finset.sum_boole]
    exact_mod_cast hdeg j
  rcases Nat.eq_zero_or_pos t with ht | ht
  · subst ht
    refine ⟨fun _ => 1, fun _ => Or.inl rfl, ?_⟩
    intro i
    have hA : ∀ j, A i j = 0 := by
      intro j
      rcases h01 i j with h | h
      · exact h
      · exfalso
        have hle := hcol j
        have hpos : 0 < ∑ i', A i' j ^ 2 := by
          apply Finset.sum_pos' (fun _ _ => sq_nonneg _)
          exact ⟨i, Finset.mem_univ _, by rw [h]; norm_num⟩
        simp at hle
        linarith
    simp [hA]
  · have htpos : (0 : ℝ) < t := by exact_mod_cast ht
    have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr htpos
    set v : Fin n → EuclideanSpace ℝ (Fin m) :=
      fun j => WithLp.toLp 2 (fun i => A i j / Real.sqrt t) with hv
    have hvn : ∀ j, ‖v j‖ ≤ 1 := by
      intro j
      rw [EuclideanSpace.norm_eq, Real.sqrt_le_one]
      have hsq : ∀ i, ‖v j i‖ ^ 2 = A i j ^ 2 / t := by
        intro i
        simp only [hv, PiLp.toLp_apply, Real.norm_eq_abs, sq_abs]
        rw [div_pow, Real.sq_sqrt htpos.le]
      simp_rw [hsq]
      rw [← Finset.sum_div, div_le_one htpos]
      exact hcol j
    obtain ⟨ε, hε, hbound⟩ := hB v hvn
    refine ⟨ε, hε, ?_⟩
    intro i
    have hb := hbound i
    have heq : ∑ j, ε j * v j i = (∑ j, A i j * ε j) / Real.sqrt t := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      simp only [hv, PiLp.toLp_apply]
      ring
    rw [heq, abs_div, abs_of_pos hst, div_le_iff₀ hst] at hb
    linarith

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ (t n m : ℕ) (A : Fin m → Fin n → ℝ),
      (∀ i j, A i j = 0 ∨ A i j = 1) →
      (∀ j, ({i | A i j = 1} : Finset (Fin m)).card ≤ t) →
      ∃ ε : Fin n → ℝ, IsSignVector ε ∧
        ∀ i, |∑ j, A i j * ε j| ≤ C * Real.sqrt (t * Real.log (n + 2)) := by
  obtain ⟨C, hC, hban⟩ := banaszczyk_bound
  refine ⟨C, hC, ?_⟩
  intro t n m A h01 hdeg
  obtain ⟨ε, hε, hb⟩ := scaling_transfer (C * Real.sqrt (Real.log (n + 2))) t n m A h01 hdeg
    (fun v hv => hban n m v hv)
  refine ⟨ε, hε, ?_⟩
  intro i
  have hlog : 0 ≤ Real.log ((n : ℝ) + 2) := by
    apply Real.log_nonneg
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  calc |∑ j, A i j * ε j| ≤ C * Real.sqrt (Real.log (n + 2)) * Real.sqrt t := hb i
    _ = C * Real.sqrt (t * Real.log (n + 2)) := by
        rw [Real.sqrt_mul (Nat.cast_nonneg t)]; ring
