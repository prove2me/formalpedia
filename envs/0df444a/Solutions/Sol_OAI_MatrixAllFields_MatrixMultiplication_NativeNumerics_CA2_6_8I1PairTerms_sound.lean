-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_6_8I1PairTerms_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:26:41.846234+00:00
-- url     : https://prove2.me/submissions/fbaa13f4-746e-4218-9396-68aeb0ed85ff

import Mathlib
import Definitions.Def_OAIQ254M008
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_CompactCertificate_entropyLookup_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA2_6_8I1PairCertificates_valid
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA2_6_8I1PairP_sound

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA2_6_8I1Pair
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
lemma CA2_6_8I1PairTerms_sound_oai (a : PairSlot × PairSlot) :
    (CA2_6_8I1PairTerms a).Encloses (Foundation.entropyTerm (CA2_6_8I1PairValue a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_6_8I1PairCertificates_valid
    (CA2_6_8I1PairCertificateIndex a) (CA2_6_8I1PairP_sound a)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_6_8I1PairTerms_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_6_8I1PairTerms_sound_oai
