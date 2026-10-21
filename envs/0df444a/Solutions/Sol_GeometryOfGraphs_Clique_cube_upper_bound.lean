-- Prove2me | solution 1 for GeometryOfGraphs.Clique.cube_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T20:41:48.430475+00:00
-- url     : https://prove2.me/submissions/b9a16422-43f1-4b19-9194-b68b4065f0f6

import Mathlib
import Definitions.Def_GeometryOfGraphs_Clique_isoDim

set_option autoImplicit false
open GeometryOfGraphs.Clique

theorem solution (n : ℕ) (hn : 0 < n) :
    ∃ φ : Fin n → (Fin (Nat.clog 2 n) → ℝ),
      ∀ i j, ‖φ i - φ j‖ = ((⊤ : SimpleGraph (Fin n)).dist i j : ℝ) := by
  let φ : Fin n → (Fin (Nat.clog 2 n) → ℝ) := fun i b => if (i : ℕ).testBit b then 1 else 0
  refine ⟨φ, fun i j => ?_⟩
  by_cases hij : i = j
  · subst hij
    simp
  · have hd : (⊤ : SimpleGraph (Fin n)).dist i j = 1 := by
      rw [SimpleGraph.dist_eq_one_iff_adj]
      simpa using hij
    rw [hd, Nat.cast_one]
    have hlt : ∀ k : Fin n, (k : ℕ) < 2 ^ Nat.clog 2 n := fun k =>
      lt_of_lt_of_le k.2 (Nat.le_pow_clog (by norm_num) n)
    obtain ⟨b, hb⟩ : ∃ b : Fin (Nat.clog 2 n), (i : ℕ).testBit b ≠ (j : ℕ).testBit b := by
      by_contra h
      push_neg at h
      apply hij
      apply Fin.ext
      apply Nat.eq_of_testBit_eq
      intro b
      by_cases hb : b < Nat.clog 2 n
      · exact h ⟨b, hb⟩
      · have hb' : Nat.clog 2 n ≤ b := not_lt.mp hb
        have hi : (i : ℕ).testBit b = false :=
          Nat.testBit_eq_false_of_lt
            (lt_of_lt_of_le (hlt i) (Nat.pow_le_pow_right (by norm_num) hb'))
        have hj : (j : ℕ).testBit b = false :=
          Nat.testBit_eq_false_of_lt
            (lt_of_lt_of_le (hlt j) (Nat.pow_le_pow_right (by norm_num) hb'))
        rw [hi, hj]
    apply le_antisymm
    · rw [pi_norm_le_iff_of_nonneg (by norm_num)]
      intro k
      simp only [Pi.sub_apply, φ, Real.norm_eq_abs]
      split_ifs <;> norm_num
    · calc (1 : ℝ) = ‖φ i b - φ j b‖ := by
            simp only [φ, Real.norm_eq_abs]
            split_ifs with h1 h2 <;> simp_all
        _ ≤ ‖φ i - φ j‖ := norm_le_pi_norm (φ i - φ j) b
