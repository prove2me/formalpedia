-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay.realApprox_eq_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:16:48.211944+00:00
-- url     : https://prove2.me/submissions/32b47988-551c-4b6a-9eea-b0635e2da929

import Mathlib
import Definitions.Def_OAIQ254M000
import Definitions.Def_OAIQ254M001

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

theorem realApprox_eq_polynomial_oai (x : ℝ) :
    realApprox 48 x =
      2 * ((x - 1) / (x + 1)) *
        polynomial (((x - 1) / (x + 1)) ^ 2) logCoefficients := by
  simp only [realApprox, sumPower]
  norm_num [Finset.sum_range_succ, logCoefficients, List.range_succ,
    polynomial, List.map_append, List.foldr_append]
  ring

end MatrixMultiplication.AllFieldCertificates.Replay

end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay.realApprox_eq_polynomial_oai := @OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay.realApprox_eq_polynomial_oai
