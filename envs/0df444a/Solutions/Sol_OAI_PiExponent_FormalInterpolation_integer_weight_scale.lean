-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.integer_weight_scale
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T02:08:15.648848+00:00
-- url     : https://prove2.me/submissions/d929714c-701e-4076-9b2a-a5aa2363b9e7

import Mathlib

open scoped BigOperators

theorem solution {d : Nat} (w : Fin d → ℚ) (hw : ∀ i, 0 < (w i : ℝ)) (D : Nat) : ∃ S : Nat, 0 < S ∧ ∃ W : Fin d → Nat, (∀ i, 0 < W i) ∧ (∀ i, (S : ℚ) * w i = (W i : ℚ)) ∧ ∀ (i : Fin d) (n : Nat) (q : Fin 0 → MvPolynomial (Fin d) ℂ), (∀ j, MvPolynomial.IsWeightedHomogeneous w (q j) ((n : ℚ) * w i - (D : ℚ))) → ∀ (j : Fin 0) (a : Fin d →₀ Nat), a ∈ (q j).support → (∑ k : Fin d, (a k : ℤ) * (W k : ℤ)) = (n : ℤ) * (W i : ℤ) - ((S * D : Nat) : ℤ) := by
  classical
  have hw' : ∀ i, 0 < w i := fun i => by exact_mod_cast hw i
  refine ⟨∏ j, (w j).den, Finset.prod_pos (fun j _ => (w j).den_pos), fun i =>
    (w i).num.toNat * ∏ j ∈ Finset.univ.erase i, (w j).den, fun i => ?_, fun i => ?_,
    fun i n q _ j => j.elim0⟩
  · apply Nat.mul_pos
    · have : 0 < (w i).num := Rat.num_pos.2 (hw' i)
      omega
    · exact Finset.prod_pos (fun j _ => (w j).den_pos)
  · have hnum : ((w i).num.toNat : ℚ) = (w i).num := by
      have : 0 ≤ (w i).num := (Rat.num_pos.2 (hw' i)).le
      exact_mod_cast Int.toNat_of_nonneg this
    push_cast
    rw [hnum, ← Finset.mul_prod_erase Finset.univ (fun j => ((w j).den : ℚ)) (Finset.mem_univ i)]
    rw [← Rat.mul_den_eq_num]
    ring
