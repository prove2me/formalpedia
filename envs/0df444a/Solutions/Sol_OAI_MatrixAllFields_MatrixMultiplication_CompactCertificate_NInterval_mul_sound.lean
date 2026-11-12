-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.CompactCertificate.NInterval.mul_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T07:12:30.510574+00:00
-- url     : https://prove2.me/submissions/14bbd57b-bd74-4df0-8d4c-082bd203e0df

import Mathlib
import Definitions.Def_OAIQ254M003

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_CertificatesReplay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section

namespace MatrixMultiplication.CompactCertificate

namespace NInterval

lemma div_floor_bounds (n d : ℕ) (hd : 0 < d) :
    ((n / d : ℕ) : ℝ) ≤ (n : ℝ) / d ∧
    (n : ℝ) / d ≤ ((n / d : ℕ) : ℝ) + 1 := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  constructor
  · apply (le_div_iff₀ hd').2
    exact_mod_cast Nat.div_mul_le_self n d
  · apply (div_le_iff₀ hd').2
    have h := Nat.lt_div_mul_add (a := n) hd
    exact_mod_cast (by simpa only [Nat.add_mul, Nat.one_mul] using h.le : n ≤ (n / d + 1) * d)

lemma nonneg {S : ℕ} {a : NInterval} {x : ℝ} (h : Encloses S a x) : 0 ≤ x :=
  (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)).trans h.1

lemma mul_sound_oai {S : ℕ} (hS : 0 < S) {a b : NInterval} {x y : ℝ}
    (hx : Encloses S a x) (hy : Encloses S b y) :
    Encloses S (mul S a b) (x * y) := by
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  have hlo := (div_floor_bounds (a.lo * b.lo) S hS).1
  have hhi := (div_floor_bounds (a.hi * b.hi) S hS).2
  unfold Encloses mul
  simp only [Nat.cast_add, Nat.cast_one]
  constructor
  · calc
      _ ≤ ((a.lo : ℝ) * b.lo / S) / S := by
        exact div_le_div_of_nonneg_right (by simpa only [Nat.cast_mul] using hlo) hS'.le
      _ = ((a.lo : ℝ) / S) * ((b.lo : ℝ) / S) := by ring
      _ ≤ x * y := mul_le_mul hx.1 hy.1 (by positivity) (nonneg hx)
  · calc
      x * y ≤ ((a.hi : ℝ) / S) * ((b.hi : ℝ) / S) :=
        mul_le_mul hx.2 hy.2 (nonneg hy) (by positivity)
      _ = ((a.hi : ℝ) * b.hi / S) / S := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (by simpa only [Nat.cast_mul] using hhi) hS'.le

end NInterval
end MatrixMultiplication.CompactCertificate

end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.CompactCertificate.NInterval.mul_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.CompactCertificate.NInterval.mul_sound_oai
