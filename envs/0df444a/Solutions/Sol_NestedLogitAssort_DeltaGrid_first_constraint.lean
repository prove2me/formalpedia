-- Prove2me | solution 1 for NestedLogitAssort.DeltaGrid.first_constraint
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:29:57.329944+00:00
-- url     : https://prove2.me/submissions/96cb65e1-1cc6-49fd-b9ad-ddd84be23c8a

import Mathlib
import Definitions.Def_NestedLogitAssort_DeltaGrid_Instance

open NestedLogitAssort.DeltaGrid in
theorem solution {M : Type*} [Fintype M] {n : ℕ} (I : Instance M n)
    (hv0 : 0 ≤ I.v0) (γbar : ℝ) (hγbar0 : 0 ≤ γbar) (δ : ℝ) (hδ : 1 < δ)
    (x : ℝ) (hx : 0 ≤ x) (y : M → ℝ) (hy : ∑ i, y i ≤ I.v0 * x) :
    ∑ i, δ ^ (γbar + 1) * y i ≤ I.v0 * (δ ^ (2 * γbar + 1) * x) := by
  rw [← Finset.mul_sum]
  have hpos : 0 < δ ^ (γbar + 1) := Real.rpow_pos_of_pos (by linarith) _
  have hle : δ ^ (γbar + 1) ≤ δ ^ (2 * γbar + 1) :=
    Real.rpow_le_rpow_of_exponent_le hδ.le (by linarith)
  have h1 : δ ^ (γbar + 1) * ∑ i, y i ≤ δ ^ (γbar + 1) * (I.v0 * x) :=
    mul_le_mul_of_nonneg_left hy hpos.le
  have h2 : δ ^ (γbar + 1) * (I.v0 * x) ≤ δ ^ (2 * γbar + 1) * (I.v0 * x) :=
    mul_le_mul_of_nonneg_right hle (mul_nonneg hv0 hx)
  calc δ ^ (γbar + 1) * ∑ i, y i ≤ δ ^ (2 * γbar + 1) * (I.v0 * x) := le_trans h1 h2
    _ = I.v0 * (δ ^ (2 * γbar + 1) * x) := by ring
