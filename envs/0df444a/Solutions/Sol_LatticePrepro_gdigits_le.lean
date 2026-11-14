-- Prove2me | solution 1 for LatticePrepro.gdigits_le
-- status  : ACCEPTED   (prove)
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:28:14.378519+00:00
-- url     : https://prove2.me/submissions/e4ec7ac2-120d-4ee2-9485-fc2c1fe9c3a3

import Mathlib
import Definitions.Def_LatticePrepro_Tables_Digits

namespace LatticePrepro end LatticePrepro

namespace LatticePrepro

lemma one_le_pow_sub_one {B m : ℕ} (hB : 2 ≤ B) (hm : 1 ≤ m) : 1 ≤ B ^ m - 1 := by
  have : B ≤ B ^ m := by
    calc B = B ^ 1 := (pow_one B).symm
      _ ≤ B ^ m := Nat.pow_le_pow_right (by omega) hm
  omega

end LatticePrepro

namespace LatticePrepro

/-- Claim A.2, second part: for `k ≤ J · (B^m - 1)`, every generalized digit is at most
`J · (B - 1)`. -/
private theorem gdigits_le {B m J k : ℕ} (hB : 2 ≤ B) (hm : 1 ≤ m) (hJ : 1 ≤ J)
    (hk : k ≤ J * (B ^ m - 1)) (h : Fin m) : gdigits B m k h ≤ J * (B - 1) := by
  have _ := hJ
  have hn : 1 ≤ B ^ m - 1 := one_le_pow_sub_one hB hm
  unfold gdigits
  have hdig : k % (B ^ m - 1) / B ^ (h : ℕ) % B ≤ B - 1 := by
    have := Nat.mod_lt (k % (B ^ m - 1) / B ^ (h : ℕ)) (show 0 < B by omega)
    omega
  have ha : k / (B ^ m - 1) ≤ J := Nat.div_le_of_le_mul (by rw [mul_comm]; exact hk)
  rcases Nat.lt_or_ge (k / (B ^ m - 1)) J with hlt | hge
  · calc k / (B ^ m - 1) * (B - 1) + k % (B ^ m - 1) / B ^ (h : ℕ) % B
        ≤ k / (B ^ m - 1) * (B - 1) + (B - 1) := Nat.add_le_add_left hdig _
      _ = (k / (B ^ m - 1) + 1) * (B - 1) := by ring
      _ ≤ J * (B - 1) := Nat.mul_le_mul_right _ hlt
  · have haJ : k / (B ^ m - 1) = J := le_antisymm ha hge
    have hkJ : k = J * (B ^ m - 1) := by
      have h1 : J * (B ^ m - 1) ≤ k := by
        rw [← haJ]; exact Nat.div_mul_le_self k (B ^ m - 1)
      omega
    have hb : k % (B ^ m - 1) = 0 := by rw [hkJ]; exact Nat.mul_mod_left _ _
    rw [haJ, hb, Nat.zero_div, Nat.zero_mod, add_zero]

end LatticePrepro

open LatticePrepro
theorem solution {B m J k : ℕ} (hB : 2 ≤ B) (hm : 1 ≤ m) (hJ : 1 ≤ J)
    (hk : k ≤ J * (B ^ m - 1)) (h : Fin m) : gdigits B m k h ≤ J * (B - 1) :=
  @LatticePrepro.gdigits_le B m J k hB hm hJ hk h
