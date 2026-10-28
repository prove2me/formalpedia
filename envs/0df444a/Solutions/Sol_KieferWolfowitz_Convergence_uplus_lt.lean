-- Prove2me | solution 1 for KieferWolfowitz.Convergence.uplus_lt
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:44:17.452129+00:00
-- url     : https://prove2.me/submissions/e9df55e5-6c85-49fa-90de-e1fa5cecd61d

import Mathlib
import Definitions.Def_KieferWolfowitz_Convergence_Model

open MeasureTheory ProbabilityTheory Filter Topology

open KieferWolfowitz.Convergence in
theorem solution (M : ℝ → ℝ) (θ β B : ℝ) (hβ : 0 < β) (hB : 0 < B)
    (hM : Unimodal M θ) (h1 : Cond1 M θ β B) (c z : ℝ) (hc : 0 < c) (hcβ : c < β / 2) :
    0 ≤ Uplus M θ c z ∧ Uplus M θ c z < 2 * B * c ^ 2 := by
  have hpos : 0 < 2 * B * c ^ 2 := by positivity
  have key : U M θ c z < 2 * B * c ^ 2 := by
    unfold U
    rcases lt_or_ge c (z - θ) with h | h
    · have hlt : M (z + c) < M (z - c) :=
        hM.2 (show θ < z - c by linarith)
          (show θ < z + c by linarith) (by linarith)
      have : (z - θ) * (M (z + c) - M (z - c)) < 0 :=
        mul_neg_of_pos_of_neg (by linarith) (by linarith)
      linarith
    rcases lt_or_ge (z - θ) (-c) with h' | h'
    · have hlt : M (z - c) < M (z + c) :=
        hM.1 (show z - c < θ by linarith)
          (show z + c < θ by linarith) (by linarith)
      have : (z - θ) * (M (z + c) - M (z - c)) < 0 :=
        mul_neg_of_neg_of_pos (by linarith) (by linarith)
      linarith
    · have hsum : |z + c - θ| + |z - c - θ| < β := by
        rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
        linarith
      have hC := h1 (z + c) (z - c) (by intro h; linarith) hsum
      have h2c : |z + c - (z - c)| = 2 * c := by
        rw [show z + c - (z - c) = 2 * c by ring, abs_of_pos (by linarith)]
      rw [h2c] at hC
      have hzθ : |z - θ| ≤ c := abs_le.mpr ⟨h', h⟩
      calc (z - θ) * (M (z + c) - M (z - c))
          ≤ |(z - θ) * (M (z + c) - M (z - c))| := le_abs_self _
        _ = |z - θ| * |M (z + c) - M (z - c)| := abs_mul _ _
        _ ≤ c * |M (z + c) - M (z - c)| :=
            mul_le_mul_of_nonneg_right hzθ (abs_nonneg _)
        _ < c * (B * (2 * c)) := mul_lt_mul_of_pos_left hC hc
        _ = 2 * B * c ^ 2 := by ring
  unfold Uplus
  exact ⟨le_max_right _ _, max_lt key hpos⟩
