-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_4_10I2PairP_check_0_5
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:31:22.57384+00:00
-- url     : https://prove2.me/submissions/4b1d5a86-6285-4257-b556-d1034f7f3f4e

import Mathlib
import Definitions.Def_OAIQ254M012

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA2_4_10I2Pair
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
lemma CA2_4_10I2PairP_check_0_5_oai : ∀ k l : Fin 6, contains (CA2_4_10I2PairRaw ((0,5),(k,l))) (CA2_4_10I2PairP ((0,5),(k,l))) = true := by
  decide +kernel

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_4_10I2PairP_check_0_5_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_4_10I2PairP_check_0_5_oai
