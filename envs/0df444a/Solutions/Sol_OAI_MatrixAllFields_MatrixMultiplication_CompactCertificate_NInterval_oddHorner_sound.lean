-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.CompactCertificate.NInterval.oddHorner_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T07:13:03.392491+00:00
-- url     : https://prove2.me/submissions/11838eaa-dbc1-4734-8155-8e02055d9818

import Mathlib
import Definitions.Def_OAIQ254M003
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_CompactCertificate_NInterval_frac_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_CompactCertificate_NInterval_mul_sound

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

lemma zero_sound (S : ℕ) : Encloses S zero 0 := by simp [Encloses, zero]

lemma add_sound {S : ℕ} {a b : NInterval} {x y : ℝ}
    (hx : Encloses S a x) (hy : Encloses S b y) :
    Encloses S (add a b) (x + y) := by
  simpa [Encloses, add, Nat.cast_add, add_div] using And.intro (add_le_add hx.1 hy.1) (add_le_add hx.2 hy.2)

lemma oddHorner_sound_oai {S : ℕ} (hS : 0 < S) {t : NInterval} {x : ℝ}
    (hx : Encloses S t x) (start n : ℕ) :
    Encloses S (oddHorner S t start n) (oddPolynomial x start n) := by
  induction n generalizing start with
  | zero => exact zero_sound S
  | succ n ih =>
    apply add_sound
    · simpa only [Nat.cast_one, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
        using (frac_sound (n := 1) hS (by omega : 0 < 2 * start + 1))
    · exact mul_sound hS hx (ih (start + 1))

end NInterval
end MatrixMultiplication.CompactCertificate

end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.CompactCertificate.NInterval.oddHorner_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.CompactCertificate.NInterval.oddHorner_sound_oai
