-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I1PairTerms_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T12:00:01.879505+00:00
-- url     : https://prove2.me/submissions/40bcd621-07fb-48ce-8762-da47d3fd7643

import Mathlib
import Definitions.Def_OAIQ254M007
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_CompactCertificate_entropyLookup_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_6_9I1PairCertificates_valid
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_6_9I1PairP_sound

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_6_9I1Pair
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
lemma CA1_6_9I1PairTerms_sound_oai (a : PairSlot × PairSlot) :
    (CA1_6_9I1PairTerms a).Encloses (Foundation.entropyTerm (CA1_6_9I1PairValue a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_6_9I1PairCertificates_valid
    (CA1_6_9I1PairCertificateIndex a) (CA1_6_9I1PairP_sound a)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I1PairTerms_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I1PairTerms_sound_oai
