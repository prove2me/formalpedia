-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball.nonnegative_radius
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T07:12:23.557496+00:00
-- url     : https://prove2.me/submissions/1c5cec76-8abe-4054-bcae-cc28dae965e2

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

theorem nonnegative_radius_oai {b : Ball} {x : ℝ} (h : b.Encloses x) : 0 ≤ b.radius := by
  have : (0 : ℝ) ≤ b.radius := (abs_nonneg _).trans h
  exact_mod_cast this

end Ball

end MatrixMultiplication.AllFieldCertificates

end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball.nonnegative_radius_oai := @OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball.nonnegative_radius_oai
