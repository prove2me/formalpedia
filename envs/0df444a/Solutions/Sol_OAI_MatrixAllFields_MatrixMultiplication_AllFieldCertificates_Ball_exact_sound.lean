-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball.exact_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T07:12:21.699477+00:00
-- url     : https://prove2.me/submissions/e645ff41-3390-4d60-bfb1-43605e82422a

import Mathlib
import Definitions.Def_OAIQ254M000

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
namespace MatrixMultiplication.AllFieldCertificates

namespace Ball

theorem exact_sound_oai (q : ℚ) : (exact q).Encloses (q : ℝ) := by
  simp [Encloses, exact]

end Ball

end MatrixMultiplication.AllFieldCertificates

end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball.exact_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball.exact_sound_oai
