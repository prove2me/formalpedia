-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_7_7I1PairTerms_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:32:20.651052+00:00
-- url     : https://prove2.me/submissions/c3c03911-f95b-45d4-af7c-9e8903c730b7

import Mathlib
import Definitions.Def_OAIQ254M012
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_CompactCertificate_entropyLookup_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA2_7_7I1PairCertificates_valid
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA2_7_7I1PairP_sound

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA2_7_7I1Pair
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
lemma CA2_7_7I1PairTerms_sound_oai (a : PairSlot × PairSlot) :
    (CA2_7_7I1PairTerms a).Encloses (Foundation.entropyTerm (CA2_7_7I1PairValue a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_7_7I1PairCertificates_valid
    (CA2_7_7I1PairCertificateIndex a) (CA2_7_7I1PairP_sound a)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_7_7I1PairTerms_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_7_7I1PairTerms_sound_oai
