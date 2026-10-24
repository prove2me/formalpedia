-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.rational_weights_common_integer_scale
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T19:42:47.659358+00:00
-- url     : https://prove2.me/submissions/0e415d43-60b9-4893-abae-4e0f8b563e53

import Mathlib

theorem solution
    {d : Nat} (w : Fin d → Rat)
    (hw : ∀ i : Fin d, 0 < (w i : Real)) :
    ∃ L : Nat, 0 < L ∧ ∃ c : Fin d → Nat,
      ∀ i : Fin d, 0 < c i ∧ (c i : Real) * (w i : Real) = (L : Real) := by
  classical
  have hwq : ∀ i, 0 < w i := fun i => by exact_mod_cast hw i
  let p : Fin d → ℕ := fun i => (w i).num.toNat
  have hp : ∀ i, 0 < p i := fun i => by
    have := Rat.num_pos.mpr (hwq i); simp only [p]; omega
  have hpw : ∀ i, (p i : ℚ) = (w i).den * w i := by
    intro i
    have h1 : ((p i : ℤ) : ℚ) = (w i).num := by
      simp only [p]; rw [Int.toNat_of_nonneg (Rat.num_pos.mpr (hwq i)).le]
    have h2 := Rat.num_div_den (w i)
    have hd : ((w i).den : ℚ) ≠ 0 := by exact_mod_cast (w i).den_nz
    push_cast at h1
    rw [h1]; field_simp at h2 ⊢; linarith [h2]
  let L : ℕ := ∏ i, p i
  have hL : 0 < L := Finset.prod_pos (fun i _ => hp i)
  refine ⟨L, hL, fun i => L / p i * (w i).den, fun i => ⟨?_, ?_⟩⟩
  · have hdiv : p i ∣ L := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    apply Nat.mul_pos (Nat.div_pos (Nat.le_of_dvd hL hdiv) (hp i)) (w i).den_pos
  · have hdiv : p i ∣ L := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    have : ((L / p i * (w i).den : ℕ) : ℚ) * w i = L := by
      push_cast
      rw [Nat.cast_div hdiv (by exact_mod_cast (hp i).ne'), mul_assoc, ← hpw i]
      field_simp [(hp i).ne']
    exact_mod_cast this
