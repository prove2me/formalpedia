-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_6_7I2PairP_check_0_0
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:33:09.407214+00:00
-- url     : https://prove2.me/submissions/916853a2-5b68-4215-b22e-f14673edcd1a

import Mathlib
import Definitions.Def_OAIQ254M012

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA3_6_7I2Pair
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
lemma CA3_6_7I2PairP_check_0_0_oai : ∀ k l : Fin 6, contains (CA3_6_7I2PairRaw ((0,0),(k,l))) (CA3_6_7I2PairP ((0,0),(k,l))) = true := by
  decide +kernel

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_6_7I2PairP_check_0_0_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_6_7I2PairP_check_0_0_oai
