-- Prove2me | solution 1 for NetworkQuality.PotentialMax.eq_13
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:28:27.509075+00:00
-- url     : https://prove2.me/submissions/6484be93-1a2d-4882-bad3-e88da8464677

import Mathlib
import Definitions.Def_NetworkQuality_PotentialMax_Setting

set_option autoImplicit false
open NetworkQuality.PotentialMax Market

theorem solution {n : ℕ} (M : Market n) (hM : M.Standing) (q : ℝ) (hq : 0 ≤ q)
    (hs : M.StrongNE q) :
    M.v ⟨0, hM.1⟩ * M.f 1 q * ∑ i : Fin n, 1 / M.v i ≤ ∑ i : Fin n, M.f (i.val + 1) q ∧
    ∑ i : Fin n, M.f (i.val + 1) q ≤
      M.v ⟨n - 1, Nat.sub_lt hM.1 Nat.one_pos⟩ * M.f n q * ∑ i : Fin n, 1 / M.v i := by
  have hv : ∀ i, 0 < M.v i := hM.2.1
  have hmono := hs.monotone
  constructor
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 : M.v ⟨0, hM.1⟩ * M.f 1 q ≤ M.v i * M.f (i.val + 1) q :=
      hmono (by simp [Fin.le_def])
    have hvi := hv i
    rw [mul_one_div, div_le_iff₀ hvi]
    linarith
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 : M.v i * M.f (i.val + 1) q ≤ M.v ⟨n - 1, Nat.sub_lt hM.1 Nat.one_pos⟩ * M.f n q := by
      have := hmono (show i ≤ ⟨n - 1, Nat.sub_lt hM.1 Nat.one_pos⟩ by
        simp only [Fin.le_def]; omega)
      have e : (n - 1) + 1 = n := Nat.sub_add_cancel hM.1
      simpa [e] using this
    have hvi := hv i
    rw [mul_one_div, le_div_iff₀ hvi]
    linarith
