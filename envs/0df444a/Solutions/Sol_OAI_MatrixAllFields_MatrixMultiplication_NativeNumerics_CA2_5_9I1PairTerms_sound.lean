-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_5_9I1PairTerms_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:32:12.125624+00:00
-- url     : https://prove2.me/submissions/4e101fd3-6189-4069-accb-ee954da83ed5

import Mathlib
import Definitions.Def_OAIQ254M012
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_CompactCertificate_entropyLookup_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA2_5_9I1PairP_check
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA2_5_9I1PairRaw_sound

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA2_5_9I1
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
lemma CA2_5_9I1PairCertificates_valid :
    CA2_5_9I1PairCertificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA2_5_9I1PairP_sound (a : PairSlot × PairSlot) :
    (CA2_5_9I1PairP a).Encloses (CA2_5_9I1PairValue a) :=
  contains_sound (CA2_5_9I1PairRaw_sound a) (CA2_5_9I1PairP_check a)
lemma CA2_5_9I1PairTerms_sound_oai (a : PairSlot × PairSlot) :
    (CA2_5_9I1PairTerms a).Encloses (Foundation.entropyTerm (CA2_5_9I1PairValue a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_5_9I1PairCertificates_valid
    (CA2_5_9I1PairCertificateIndex a) (CA2_5_9I1PairP_sound a)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_5_9I1PairTerms_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_5_9I1PairTerms_sound_oai
