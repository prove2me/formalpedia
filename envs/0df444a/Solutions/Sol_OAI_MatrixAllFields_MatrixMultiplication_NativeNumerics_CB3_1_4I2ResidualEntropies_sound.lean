-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_1_4I2ResidualEntropies_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T14:14:59.973181+00:00
-- url     : https://prove2.me/submissions/b3280aa8-6931-4ab8-95fe-0786d9ea2c11

import Mathlib
import Definitions.Def_OAIQ254M010
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkLog_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_finSumBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_CompactCertificate_entropyLookup_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_1_4I2R0Raw_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_1_4I2R10H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_1_4I2R11H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_1_4I2R12H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_1_4I2R13H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_1_4I2R14H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_1_4I2R15H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_1_4I2R16H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_1_4I2R1Mass_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_1_4I2R1Raw_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_1_4I2R2Entropy_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_1_4I2R2MassTerm_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_1_4I2R3H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_1_4I2R4H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_1_4I2R5H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_1_4I2R6H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_1_4I2R7MassTerm_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_1_4I2R7Terms_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_1_4I2R8MassTerm_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_1_4I2R8Terms_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_1_4I2R9MassTerm_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_1_4I2R9P_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_entropyTerm_ball
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_homogeneous_enclosed

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SparseContraction
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
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

lemma entropyFin_enclosed (n : ℕ) (p : Fin n → ℝ) (bs : Fin n → Ball)
    (h : ∀ i, (bs i).Encloses (Foundation.entropyTerm (p i))) :
    (finSumBall n bs).Encloses (Foundation.finiteEntropy p) :=
  finSumBall_sound n _ _ h

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB3_1_4I2
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
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
lemma CB3_1_4I2R0Certificates_valid :
    CB3_1_4I2R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB3_1_4I2R0P_check : ∀ a : Fin 6, contains (CB3_1_4I2R0Raw a) (CB3_1_4I2R0P a) = true := by
  decide +kernel
lemma CB3_1_4I2R0P_sound (a : Fin 6) :
    (CB3_1_4I2R0P a).Encloses (CB3_1_4I2R0Value a) :=
  contains_sound (CB3_1_4I2R0Raw_sound a) (CB3_1_4I2R0P_check a)
lemma CB3_1_4I2R0Terms_sound (a : Fin 6) :
    (CB3_1_4I2R0Terms a).Encloses (Foundation.entropyTerm (CB3_1_4I2R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_1_4I2R0Certificates_valid
    (CB3_1_4I2R0CertificateIndex a) (CB3_1_4I2R0P_sound a)
lemma CB3_1_4I2R0Entropy_sound : CB3_1_4I2R0Entropy.Encloses (Foundation.finiteEntropy CB3_1_4I2R0Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_1_4I2R0Value CB3_1_4I2R0Terms CB3_1_4I2R0Terms_sound) (by decide +kernel)
lemma CB3_1_4I2R0Mass_sound : CB3_1_4I2R0Mass.Encloses (∑ a, CB3_1_4I2R0Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_1_4I2R0P CB3_1_4I2R0Value CB3_1_4I2R0P_sound) (by decide +kernel)
lemma CB3_1_4I2R0MassTermLog_sound : CB3_1_4I2R0MassTermLog.Encloses (Real.log ((∑ a, CB3_1_4I2R0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB3_1_4I2R0Mass_sound) (w := CB3_1_4I2R0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CB3_1_4I2R0MassTerm_sound : CB3_1_4I2R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_1_4I2R0Value a))) := by
  exact contains_sound (entropyTerm_ball (CB3_1_4I2R0Mass_sound) CB3_1_4I2R0MassTermLog_sound) (by decide +kernel)
lemma CB3_1_4I2R0H_sound : CB3_1_4I2R0H.Encloses (homogeneousEntropy CB3_1_4I2R0Value) := by
  exact contains_sound (homogeneous_enclosed CB3_1_4I2R0Value CB3_1_4I2R0MassTerm_sound CB3_1_4I2R0Entropy_sound) (by decide +kernel)
lemma CB3_1_4I2R1Certificates_valid :
    CB3_1_4I2R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB3_1_4I2R1P_check : ∀ a : Fin 6, contains (CB3_1_4I2R1Raw a) (CB3_1_4I2R1P a) = true := by
  decide +kernel
lemma CB3_1_4I2R1P_sound (a : Fin 6) :
    (CB3_1_4I2R1P a).Encloses (CB3_1_4I2R1Value a) :=
  contains_sound (CB3_1_4I2R1Raw_sound a) (CB3_1_4I2R1P_check a)
lemma CB3_1_4I2R1Terms_sound (a : Fin 6) :
    (CB3_1_4I2R1Terms a).Encloses (Foundation.entropyTerm (CB3_1_4I2R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_1_4I2R1Certificates_valid
    (CB3_1_4I2R1CertificateIndex a) (CB3_1_4I2R1P_sound a)
lemma CB3_1_4I2R1Entropy_sound : CB3_1_4I2R1Entropy.Encloses (Foundation.finiteEntropy CB3_1_4I2R1Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_1_4I2R1Value CB3_1_4I2R1Terms CB3_1_4I2R1Terms_sound) (by decide +kernel)
lemma CB3_1_4I2R1MassTermLog_sound : CB3_1_4I2R1MassTermLog.Encloses (Real.log ((∑ a, CB3_1_4I2R1Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB3_1_4I2R1Mass_sound) (w := CB3_1_4I2R1MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CB3_1_4I2R1MassTerm_sound : CB3_1_4I2R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_1_4I2R1Value a))) := by
  exact contains_sound (entropyTerm_ball (CB3_1_4I2R1Mass_sound) CB3_1_4I2R1MassTermLog_sound) (by decide +kernel)
lemma CB3_1_4I2R1H_sound : CB3_1_4I2R1H.Encloses (homogeneousEntropy CB3_1_4I2R1Value) := by
  exact contains_sound (homogeneous_enclosed CB3_1_4I2R1Value CB3_1_4I2R1MassTerm_sound CB3_1_4I2R1Entropy_sound) (by decide +kernel)
lemma CB3_1_4I2R2H_sound : CB3_1_4I2R2H.Encloses (homogeneousEntropy CB3_1_4I2R2Value) := by
  exact contains_sound (homogeneous_enclosed CB3_1_4I2R2Value CB3_1_4I2R2MassTerm_sound CB3_1_4I2R2Entropy_sound) (by decide +kernel)
lemma CB3_1_4I2R7Entropy_sound : CB3_1_4I2R7Entropy.Encloses (Foundation.finiteEntropy CB3_1_4I2R7Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_1_4I2R7Value CB3_1_4I2R7Terms CB3_1_4I2R7Terms_sound) (by decide +kernel)
lemma CB3_1_4I2R7H_sound : CB3_1_4I2R7H.Encloses (homogeneousEntropy CB3_1_4I2R7Value) := by
  exact contains_sound (homogeneous_enclosed CB3_1_4I2R7Value CB3_1_4I2R7MassTerm_sound CB3_1_4I2R7Entropy_sound) (by decide +kernel)
lemma CB3_1_4I2R8Entropy_sound : CB3_1_4I2R8Entropy.Encloses (Foundation.finiteEntropy CB3_1_4I2R8Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_1_4I2R8Value CB3_1_4I2R8Terms CB3_1_4I2R8Terms_sound) (by decide +kernel)
lemma CB3_1_4I2R8H_sound : CB3_1_4I2R8H.Encloses (homogeneousEntropy CB3_1_4I2R8Value) := by
  exact contains_sound (homogeneous_enclosed CB3_1_4I2R8Value CB3_1_4I2R8MassTerm_sound CB3_1_4I2R8Entropy_sound) (by decide +kernel)
lemma CB3_1_4I2R9Certificates_valid :
    CB3_1_4I2R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB3_1_4I2R9Terms_sound (a : Fin 6) :
    (CB3_1_4I2R9Terms a).Encloses (Foundation.entropyTerm (CB3_1_4I2R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_1_4I2R9Certificates_valid
    (CB3_1_4I2R9CertificateIndex a) (CB3_1_4I2R9P_sound a)
lemma CB3_1_4I2R9Entropy_sound : CB3_1_4I2R9Entropy.Encloses (Foundation.finiteEntropy CB3_1_4I2R9Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_1_4I2R9Value CB3_1_4I2R9Terms CB3_1_4I2R9Terms_sound) (by decide +kernel)
lemma CB3_1_4I2R9H_sound : CB3_1_4I2R9H.Encloses (homogeneousEntropy CB3_1_4I2R9Value) := by
  exact contains_sound (homogeneous_enclosed CB3_1_4I2R9Value CB3_1_4I2R9MassTerm_sound CB3_1_4I2R9Entropy_sound) (by decide +kernel)
lemma CB3_1_4I2ResidualEntropies_sound_oai (k : Fin 17) :
    (CB3_1_4I2ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 3 1 4)) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 2 (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) k)) := by
  fin_cases k
  · exact CB3_1_4I2R0H_sound
  · exact CB3_1_4I2R1H_sound
  · exact CB3_1_4I2R2H_sound
  · exact CB3_1_4I2R3H_sound
  · exact CB3_1_4I2R4H_sound
  · exact CB3_1_4I2R5H_sound
  · exact CB3_1_4I2R6H_sound
  · exact CB3_1_4I2R7H_sound
  · exact CB3_1_4I2R8H_sound
  · exact CB3_1_4I2R9H_sound
  · exact CB3_1_4I2R10H_sound
  · exact CB3_1_4I2R11H_sound
  · exact CB3_1_4I2R12H_sound
  · exact CB3_1_4I2R13H_sound
  · exact CB3_1_4I2R14H_sound
  · exact CB3_1_4I2R15H_sound
  · exact CB3_1_4I2R16H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_1_4I2ResidualEntropies_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_1_4I2ResidualEntropies_sound_oai
