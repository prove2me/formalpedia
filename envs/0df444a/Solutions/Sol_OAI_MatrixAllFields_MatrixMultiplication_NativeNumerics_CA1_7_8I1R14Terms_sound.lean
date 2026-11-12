-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I1R14Terms_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T12:08:38.487123+00:00
-- url     : https://prove2.me/submissions/90ba7139-8b42-4dd0-b6c5-fb89434a36c5

import Mathlib
import Definitions.Def_OAIQ254M007
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_CompactCertificate_entropyLookup_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_7_8I1R14P_sound

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_7_8I1
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
lemma CA1_7_8I1R14Certificates_valid :
    CA1_7_8I1R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA1_7_8I1R14Terms_sound_oai (a : PairSlot) :
    (CA1_7_8I1R14Terms a).Encloses (Foundation.entropyTerm (CA1_7_8I1R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_7_8I1R14Certificates_valid
    (CA1_7_8I1R14CertificateIndex a) (CA1_7_8I1R14P_sound a)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I1R14Terms_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I1R14Terms_sound_oai
