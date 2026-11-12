-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_5_9I2PairTerms_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:24:47.560128+00:00
-- url     : https://prove2.me/submissions/48f8868e-6a96-4e89-b140-57c00cc6a29c

import Mathlib
import Definitions.Def_OAIQ254M008
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_CompactCertificate_entropyLookup_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA2_5_9I2PairP_sound

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA2_5_9I2Pair
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
lemma CA2_5_9I2PairCertificates_valid :
    CA2_5_9I2PairCertificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA2_5_9I2PairTerms_sound_oai (a : PairSlot × PairSlot) :
    (CA2_5_9I2PairTerms a).Encloses (Foundation.entropyTerm (CA2_5_9I2PairValue a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_5_9I2PairCertificates_valid
    (CA2_5_9I2PairCertificateIndex a) (CA2_5_9I2PairP_sound a)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_5_9I2PairTerms_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_5_9I2PairTerms_sound_oai
