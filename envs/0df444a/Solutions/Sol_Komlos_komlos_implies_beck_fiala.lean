-- Prove2me | solution 1 for Komlos.komlos_implies_beck_fiala
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T02:06:10.901808+00:00
-- url     : https://prove2.me/submissions/d236dc39-f7b7-4d7d-b9d8-2f2f9ba0ecb5

import Mathlib
import Definitions.Def_Komlos_model

open Komlos

theorem solution (K : ℝ) (hK : KomlosBound K)
    (t n m : ℕ) (A : Fin m → Fin n → ℝ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hdeg : ∀ j, ({i | A i j = 1} : Finset (Fin m)).card ≤ t) :
    ∃ ε : Fin n → ℝ, IsSignVector ε ∧
      ∀ i, |∑ j, A i j * ε j| ≤ K * Real.sqrt t := by
  -- Each column has squared Euclidean norm equal to its number of ones, hence at most `t`.
  have hcol : ∀ j, ∑ i, A i j ^ 2 ≤ (t : ℝ) := by
    intro j
    have h1 : ∑ i, A i j ^ 2 = ∑ i, (if A i j = 1 then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      rcases h01 i j with h | h <;> simp [h]
    rw [h1, Finset.sum_boole]
    exact_mod_cast hdeg j
  rcases Nat.eq_zero_or_pos t with ht | ht
  · -- Degenerate case `t = 0`: the matrix vanishes identically.
    subst ht
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
  · -- Main case: scale the columns by `1 / √t` and invoke the Komlós property.
    have htpos : (0 : ℝ) < t := by exact_mod_cast ht
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
    obtain ⟨ε, hε, hbound⟩ := hK n m v hvn
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
