-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_2_13I1R4Terms_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:40:57.257104+00:00
-- url     : https://prove2.me/submissions/24d09655-5e7e-4ba1-8d2f-bf5456be9e27

import Mathlib
import Definitions.Def_OAIQ254M007
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_CompactCertificate_entropyLookup_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_2_13I1R4P_sound

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_2_13I1
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
lemma CA1_2_13I1R4Certificates_valid :
    CA1_2_13I1R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA1_2_13I1R4Terms_sound_oai (a : PairSlot) :
    (CA1_2_13I1R4Terms a).Encloses (Foundation.entropyTerm (CA1_2_13I1R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_2_13I1R4Certificates_valid
    (CA1_2_13I1R4CertificateIndex a) (CA1_2_13I1R4P_sound a)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_2_13I1R4Terms_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_2_13I1R4Terms_sound_oai
