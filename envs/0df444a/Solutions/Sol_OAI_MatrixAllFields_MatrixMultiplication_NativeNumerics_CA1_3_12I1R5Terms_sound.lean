-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_3_12I1R5Terms_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:44:29.748257+00:00
-- url     : https://prove2.me/submissions/050de035-1035-4bf6-99a5-c2b656c61f6d

import Mathlib
import Definitions.Def_OAIQ254M007
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_CompactCertificate_entropyLookup_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_3_12I1R5Raw_sound

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_3_12I1
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
lemma CA1_3_12I1R5Certificates_valid :
    CA1_3_12I1R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA1_3_12I1R5P_check : ∀ a : PairSlot, contains (CA1_3_12I1R5Raw a) (CA1_3_12I1R5P a) = true := by
  decide +kernel
lemma CA1_3_12I1R5P_sound (a : PairSlot) :
    (CA1_3_12I1R5P a).Encloses (CA1_3_12I1R5Value a) :=
  contains_sound (CA1_3_12I1R5Raw_sound a) (CA1_3_12I1R5P_check a)
lemma CA1_3_12I1R5Terms_sound_oai (a : PairSlot) :
    (CA1_3_12I1R5Terms a).Encloses (Foundation.entropyTerm (CA1_3_12I1R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_3_12I1R5Certificates_valid
    (CA1_3_12I1R5CertificateIndex a) (CA1_3_12I1R5P_sound a)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_3_12I1R5Terms_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_3_12I1R5Terms_sound_oai
