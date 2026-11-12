-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I1R9Terms_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:30:03.389428+00:00
-- url     : https://prove2.me/submissions/0f32362d-50ab-4fa4-afb9-c2d3954fc037

import Mathlib
import Definitions.Def_OAIQ254M012
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_CompactCertificate_entropyLookup_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_7_8I1R9Raw_sound

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
lemma CA1_7_8I1R9Certificates_valid :
    CA1_7_8I1R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA1_7_8I1R9P_check : ∀ a : PairSlot, contains (CA1_7_8I1R9Raw a) (CA1_7_8I1R9P a) = true := by
  decide +kernel
lemma CA1_7_8I1R9P_sound (a : PairSlot) :
    (CA1_7_8I1R9P a).Encloses (CA1_7_8I1R9Value a) :=
  contains_sound (CA1_7_8I1R9Raw_sound a) (CA1_7_8I1R9P_check a)
lemma CA1_7_8I1R9Terms_sound_oai (a : PairSlot) :
    (CA1_7_8I1R9Terms a).Encloses (Foundation.entropyTerm (CA1_7_8I1R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_7_8I1R9Certificates_valid
    (CA1_7_8I1R9CertificateIndex a) (CA1_7_8I1R9P_sound a)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I1R9Terms_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I1R9Terms_sound_oai
