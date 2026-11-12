-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I2PairTerms_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:24:06.504471+00:00
-- url     : https://prove2.me/submissions/fa3a4ad3-ce3b-4792-8153-987ee766187c

import Mathlib
import Definitions.Def_OAIQ254M008
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_CompactCertificate_entropyLookup_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_7_8I2PairP_sound

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_7_8I2Pair
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
lemma CA1_7_8I2PairCertificates_valid :
    CA1_7_8I2PairCertificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA1_7_8I2PairTerms_sound_oai (a : PairSlot × PairSlot) :
    (CA1_7_8I2PairTerms a).Encloses (Foundation.entropyTerm (CA1_7_8I2PairValue a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_7_8I2PairCertificates_valid
    (CA1_7_8I2PairCertificateIndex a) (CA1_7_8I2PairP_sound a)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I2PairTerms_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I2PairTerms_sound_oai
