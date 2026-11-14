-- Prove2me | solution 1 for LatticePrepro.digitVal_gdigits
-- status  : ACCEPTED   (prove)
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:28:13.688121+00:00
-- url     : https://prove2.me/submissions/f1bbd8ba-bdbe-4b03-b5a2-1054cea0961c

import Mathlib
import Definitions.Def_LatticePrepro_Tables_Digits

namespace LatticePrepro end LatticePrepro

namespace LatticePrepro

/-- The geometric identity `(B - 1) · ∑_{h<m} B^h + 1 = B^m`, without subtraction. -/
lemma pred_mul_geomSum_add_one {B : ℕ} (hB : 1 ≤ B) (m : ℕ) :
    (B - 1) * (∑ h ∈ Finset.range m, B ^ h) + 1 = B ^ m := by
  obtain ⟨B', rfl⟩ : ∃ B', B = B' + 1 := ⟨B - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, add_right_comm, ih, pow_succ]
    ring

/-- The geometric identity `(B - 1) · ∑_{h<m} B^h = B^m - 1`. -/
lemma pred_mul_geomSum {B : ℕ} (hB : 1 ≤ B) (m : ℕ) :
    (B - 1) * (∑ h ∈ Finset.range m, B ^ h) = B ^ m - 1 := by
  have := pred_mul_geomSum_add_one hB m
  omega

/-- The base-`B` digit expansion of `b` up to `m` digits recovers `b mod B^m`. -/
lemma sum_digit_mul_pow {B : ℕ} (b m : ℕ) :
    ∑ h ∈ Finset.range m, (b / B ^ h % B) * B ^ h = b % B ^ m := by
  induction m with
  | zero => simp [Nat.mod_one]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, Nat.mod_pow_succ, mul_comm]

lemma one_le_pow_sub_one {B m : ℕ} (hB : 2 ≤ B) (hm : 1 ≤ m) : 1 ≤ B ^ m - 1 := by
  have : B ≤ B ^ m := by
    calc B = B ^ 1 := (pow_one B).symm
      _ ≤ B ^ m := Nat.pow_le_pow_right (by omega) hm
  omega

end LatticePrepro

namespace LatticePrepro

/-- Claim A.2, first part: `val B (gdigits B m k) = k`. -/
private theorem digitVal_gdigits {B m : ℕ} (hB : 2 ≤ B) (hm : 1 ≤ m) (k : ℕ) :
    digitVal B (gdigits B m k) = k := by
  have hn : 1 ≤ B ^ m - 1 := one_le_pow_sub_one hB hm
  set a := k / (B ^ m - 1) with ha
  set b := k % (B ^ m - 1) with hb
  have hbl : b < B ^ m := by
    have := Nat.mod_lt k (show 0 < B ^ m - 1 by omega)
    omega
  unfold digitVal gdigits
  rw [Fin.sum_univ_eq_sum_range (fun h => (a * (B - 1) + b / B ^ h % B) * B ^ h) m]
  simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, mul_assoc]
  rw [sum_digit_mul_pow, Nat.mod_eq_of_lt hbl, pred_mul_geomSum (by omega)]
  rw [ha, hb, Nat.div_add_mod']

end LatticePrepro

open LatticePrepro
theorem solution {B m : ℕ} (hB : 2 ≤ B) (hm : 1 ≤ m) (k : ℕ) :
    digitVal B (gdigits B m k) = k :=
  @LatticePrepro.digitVal_gdigits B m hB hm k
