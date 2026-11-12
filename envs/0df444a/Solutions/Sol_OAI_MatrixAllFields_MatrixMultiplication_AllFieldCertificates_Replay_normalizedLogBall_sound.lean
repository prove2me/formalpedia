-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay.normalizedLogBall_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T07:12:24.347198+00:00
-- url     : https://prove2.me/submissions/099f1cdd-1917-4f5d-892b-ae0ee28bf1fc

import Mathlib
import Definitions.Def_OAIQ254M000
import Definitions.Def_OAIQ254M001
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_mul_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkPolynomial_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_normalized_log_error_48
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_pad_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_realApprox_eq_polynomial

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
namespace MatrixMultiplication.AllFieldCertificates.Replay

open MatrixMultiplication.Foundation.RationalLogCertificate

theorem normalizedLogBall_sound_oai {m : ℚ} {trace : List Ball}
    (hlo : 1 ≤ m) (hhi : m ≤ 2)
    (hc : checkPolynomial (.exact (logVariable m ^ 2)) logCoefficients trace = true) :
    (normalizedLogBall m trace).Encloses (Real.log (m : ℝ)) := by
  have hp := checkPolynomial_sound (Ball.exact_sound (logVariable m ^ 2))
    logCoefficients trace hc
  have hv : (logVariable m : ℝ) = ((m : ℝ) - 1) / ((m : ℝ) + 1) := by
    simp [logVariable]
  have ha : (Ball.mul (.exact (2 * logVariable m)) (traceHead trace)).Encloses
      (realApprox 48 (m : ℝ)) := by
    rw [realApprox_eq_polynomial]
    convert Ball.mul_sound (Ball.exact_sound (2 * logVariable m)) hp using 1
    all_goals try with_reducible_and_instances rfl
    simp [hv]
  apply pad_sound ha
  have h := (normalized_log_error_48 (m : ℝ)
    (by exact_mod_cast hlo) (by exact_mod_cast hhi)).le
  simpa using h

end MatrixMultiplication.AllFieldCertificates.Replay

end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay.normalizedLogBall_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay.normalizedLogBall_sound_oai
