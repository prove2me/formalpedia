-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.CompactCertificate.logApprox_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T07:13:06.362205+00:00
-- url     : https://prove2.me/submissions/c82967cd-a4ae-4b2e-9cbb-a01c364838a6

import Mathlib
import Definitions.Def_OAIQ254M003
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_realApprox_eq_polynomial
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_CompactCertificate_NInterval_frac_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_CompactCertificate_NInterval_mul_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_CompactCertificate_NInterval_oddHorner_sound

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

lemma add_sound {S : ℕ} {a b : NInterval} {x y : ℝ}
    (hx : Encloses S a x) (hy : Encloses S b y) :
    Encloses S (add a b) (x + y) := by
  simpa [Encloses, add, Nat.cast_add, add_div] using And.intro (add_le_add hx.1 hy.1) (add_le_add hx.2 hy.2)

end NInterval
end MatrixMultiplication.CompactCertificate

namespace MatrixMultiplication.CompactCertificate
open AllFieldCertificates AllFieldCertificates.Replay
open Foundation.RationalLogCertificate

lemma oddPolynomial_eq (x : ℝ) :
    NInterval.oddPolynomial x 0 24 = polynomial x logCoefficients := by
  norm_num [NInterval.oddPolynomial, polynomial, logCoefficients, List.range_succ]

lemma scale_pos : 0 < scale := by decide

lemma logApprox_sound_oai {n d : ℕ} (hd : 0 < d) (hlo : d ≤ n) :
    (logApprox n d).Encloses scale (realApprox 48 ((n : ℝ) / d)) := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hsum : 0 < n + d := by omega
  have hu := NInterval.frac_sound (n := n - d) scale_pos hsum
  have heq : (((n : ℝ) / d - 1) / ((n : ℝ) / d + 1)) =
      ((n - d : ℕ) : ℝ) / (n + d : ℕ) := by
    rw [Nat.cast_sub hlo, Nat.cast_add]
    field_simp
  rw [realApprox_eq_polynomial, heq, ← oddPolynomial_eq]
  simpa only [logApprox, two_mul, pow_two] using
    NInterval.mul_sound scale_pos (NInterval.add_sound hu hu)
      (NInterval.oddHorner_sound scale_pos (NInterval.mul_sound scale_pos hu hu) 0 24)

end MatrixMultiplication.CompactCertificate

end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.CompactCertificate.logApprox_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.CompactCertificate.logApprox_sound_oai
