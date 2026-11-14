-- Prove2me | solution 1 for LatticePrepro.exists_pow_between
-- status  : ACCEPTED   (prove)
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:27:58.502226+00:00
-- url     : https://prove2.me/submissions/3741f43b-2b17-456d-baad-e4e9673dc895

import Mathlib


namespace LatticePrepro

/-- A power of `p` in a prescribed range. -/
private lemma exists_pow_between {p N : ℕ} (hp : 2 ≤ p) (hN : 2 ≤ N) :
    ∃ d, 1 ≤ d ∧ N ≤ p ^ d ∧ p ^ d < p * N := by
  classical
  have hex : ∃ d, N ≤ p ^ d := ⟨N, (Nat.lt_pow_self (by omega : 1 < p)).le⟩
  let d := Nat.find hex
  have hd : N ≤ p ^ d := Nat.find_spec hex
  have hd1 : 1 ≤ d := by
    by_contra h0
    have h0' : d = 0 := by omega
    rw [h0', pow_zero] at hd
    omega
  have hmin : ¬ N ≤ p ^ (d - 1) := Nat.find_min hex (by omega)
  refine ⟨d, hd1, hd, ?_⟩
  have hsplit : p ^ d = p * p ^ (d - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hsplit]
  exact (Nat.mul_lt_mul_left (by omega)).mpr (by omega)

end LatticePrepro

theorem solution {p N : ℕ} (hp : 2 ≤ p) (hN : 2 ≤ N) :
    ∃ d, 1 ≤ d ∧ N ≤ p ^ d ∧ p ^ d < p * N :=
  @LatticePrepro.exists_pow_between p N hp hN
