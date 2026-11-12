-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.CompactCertificate.NInterval.frac_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T07:12:29.58604+00:00
-- url     : https://prove2.me/submissions/28d5de3f-fe7d-4325-b18b-c430fc058334

import Mathlib
import Definitions.Def_OAIQ254M003

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_CertificatesReplay
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons
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

lemma frac_sound_oai {S n d : ℕ} (hS : 0 < S) (hd : 0 < d) :
    Encloses S (frac S n d) ((n : ℝ) / d) := by
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  have hb := div_floor_bounds (n * S) d hd
  unfold Encloses frac
  simp only [Nat.cast_add, Nat.cast_one]
  constructor
  · calc
      _ ≤ ((n : ℝ) * S / d) / S :=
        div_le_div_of_nonneg_right (by simpa only [Nat.cast_mul] using hb.1) hS'.le
      _ = _ := by field_simp
  · calc
      (n : ℝ) / d = ((n : ℝ) * S / d) / S := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right (by simpa only [Nat.cast_mul] using hb.2) hS'.le

end NInterval
end MatrixMultiplication.CompactCertificate

end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.CompactCertificate.NInterval.frac_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.CompactCertificate.NInterval.frac_sound_oai
