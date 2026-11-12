-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_4_10I2PairP_check_0_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:30:18.768054+00:00
-- url     : https://prove2.me/submissions/014c0505-f28e-4391-8792-cf7b2e422b62

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
lemma CA2_4_10I2PairP_check_0_3_oai : ∀ k l : Fin 6, contains (CA2_4_10I2PairRaw ((0,3),(k,l))) (CA2_4_10I2PairP ((0,3),(k,l))) = true := by
  decide +kernel

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_4_10I2PairP_check_0_3_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_4_10I2PairP_check_0_3_oai
