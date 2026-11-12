-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_4_8I2PairRaw_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:33:50.399165+00:00
-- url     : https://prove2.me/submissions/5df1de07-8589-487b-a6d9-8a2f28d255b8

import Mathlib
import Definitions.Def_OAIQ254M012
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_A4_4_8Law_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_stageAPairBall_sound

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA4_4_8I2Pair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
lemma CA4_4_8I2PairRaw_sound_oai (a : PairSlot × PairSlot) :
    (CA4_4_8I2PairRaw a).Encloses (CA4_4_8I2PairValue a) := by
  exact stageAPairBall_sound (shape 4 4 8) (by decide +kernel) A4_4_8Law (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (fun u _ => A4_4_8Law_sound u) 2 a

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_4_8I2PairRaw_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_4_8I2PairRaw_sound_oai
