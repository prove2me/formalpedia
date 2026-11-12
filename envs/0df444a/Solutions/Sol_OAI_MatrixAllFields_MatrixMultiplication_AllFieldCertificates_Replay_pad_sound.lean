-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay.pad_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T07:12:25.19957+00:00
-- url     : https://prove2.me/submissions/8bd49ea5-fb1e-40e4-a1b6-55da05257792

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
namespace MatrixMultiplication.AllFieldCertificates.Replay

theorem pad_sound_oai {b : Ball} {x y : ℝ} {error : ℚ}
    (hx : b.Encloses x) (hxy : |y - x| ≤ (error : ℝ)) :
    (pad b error).Encloses y := by
  unfold Ball.Encloses pad at *
  simp only [Rat.cast_add]
  calc
    _ = |(y - x) + (x - (b.center : ℝ))| := by congr 1; ring
    _ ≤ |y - x| + |x - (b.center : ℝ)| := abs_add_le _ _
    _ ≤ (error : ℝ) + (b.radius : ℝ) := add_le_add hxy hx
    _ = _ := by ring

end MatrixMultiplication.AllFieldCertificates.Replay

end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay.pad_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay.pad_sound_oai
