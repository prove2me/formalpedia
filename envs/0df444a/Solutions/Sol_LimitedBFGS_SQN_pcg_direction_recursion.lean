-- Prove2me | solution 1 for LimitedBFGS.SQN.pcg_direction_recursion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T06:57:51.252575+00:00
-- url     : https://prove2.me/submissions/23160a8f-f55a-4b16-b4ec-be77d6b4573c

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_pcgIter

open Matrix
open LimitedBFGS.SQN

/-- The direction recurrence in the form the reduction needs: for `i ≠ j` and
`0 < j`, `g_i ⬝ᵥ d_j = -(g_i ⬝ᵥ (H0 *ᵥ g_j)) + beta * (g_i ⬝ᵥ d_{j-1})`, where
`beta` is the step coefficient the definition attaches to the move from
`pcgIter … (j - 1)` to `pcgIter … j`.  This is what makes the second relation of
eq. (16) a downward induction on `j` from the first one. -/
theorem pcg_direction_recursion {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (b : Fin n → ℝ) (H₀ : Matrix (Fin n) (Fin n) ℝ) (x₀ : Fin n → ℝ) (i j : ℕ) (hne : i ≠ j)
    (hj : 0 < j) :
    let stp := pcgIter A b H₀ x₀ (j - 1)
    let gj := grad A b (pcgIter A b H₀ x₀ j).x
    let gp := grad A b stp.x
    let y := gj - gp
    grad A b (pcgIter A b H₀ x₀ i).x ⬝ᵥ (pcgIter A b H₀ x₀ j).d
      = -(grad A b (pcgIter A b H₀ x₀ i).x ⬝ᵥ (H₀ *ᵥ gj))
        + ((y ⬝ᵥ (H₀ *ᵥ gj)) / (y ⬝ᵥ stp.d))
            * (grad A b (pcgIter A b H₀ x₀ i).x ⬝ᵥ stp.d) := by
  classical
  set stp := pcgIter A b H₀ x₀ (j - 1) with hstp
  set gj := grad A b (pcgIter A b H₀ x₀ j).x with hgj
  set gp := grad A b stp.x with hgp
  set y := gj - gp with hy
  set Hj := H₀ *ᵥ gj with hHj
  -- The successor iterate produced by the step taken at `j - 1`.
  set xp := stp.x + exactStep A b stp.x stp.d • stp.d with hxp
  have hgj' : grad A b xp = gj := by
    rw [hxp]
    show grad A b (pcgIter A b H₀ x₀ (j - 1 + 1)).x = gj
    rw [show j - 1 + 1 = j from by omega, hgj]
  set Hq := H₀ *ᵥ grad A b xp with hHq
  set z := grad A b xp - gp with hz
  have hj1 : j - 1 + 1 = j := by omega
  have hunf : pcgIter A b H₀ x₀ j
      = ⟨xp, -Hq + ((z ⬝ᵥ Hq) / (z ⬝ᵥ stp.d)) • stp.d⟩ := by
    have hraw : pcgIter A b H₀ x₀ (j - 1 + 1)
        = ⟨xp, -Hq + ((z ⬝ᵥ Hq) / (z ⬝ᵥ stp.d)) • stp.d⟩ := by
      have hxcomp :
          (pcgIter A b H₀ x₀ (j - 1)).x
              + exactStep A b (pcgIter A b H₀ x₀ (j - 1)).x
                  (pcgIter A b H₀ x₀ (j - 1)).d
                • (pcgIter A b H₀ x₀ (j - 1)).d = xp := by
        rw [hxp]
      simp only [pcgIter, hstp, hgp, ← hHq, ← hz, hgj']
      rw [← hxcomp]
    simpa only [hj1] using hraw
  rw [hunf, hz]
  simp only [hy, ← hgj', ← hgp]
  simp only [dotProduct_add, dotProduct_neg, dotProduct_smul, smul_eq_mul]
  ring
theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (b : Fin n → ℝ) (H₀ : Matrix (Fin n) (Fin n) ℝ) (x₀ : Fin n → ℝ) (i j : ℕ) (hne : i ≠ j)
    (hj : 0 < j) :
    let stp := pcgIter A b H₀ x₀ (j - 1)
    let gj := grad A b (pcgIter A b H₀ x₀ j).x
    let gp := grad A b stp.x
    let y := gj - gp
    grad A b (pcgIter A b H₀ x₀ i).x ⬝ᵥ (pcgIter A b H₀ x₀ j).d
      = -(grad A b (pcgIter A b H₀ x₀ i).x ⬝ᵥ (H₀ *ᵥ gj))
        + ((y ⬝ᵥ (H₀ *ᵥ gj)) / (y ⬝ᵥ stp.d))
            * (grad A b (pcgIter A b H₀ x₀ i).x ⬝ᵥ stp.d) :=
  pcg_direction_recursion A hA b H₀ x₀ i j hne hj
