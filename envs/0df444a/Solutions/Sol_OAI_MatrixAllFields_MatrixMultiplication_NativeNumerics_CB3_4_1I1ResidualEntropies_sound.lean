-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_4_1I1ResidualEntropies_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T14:36:20.718596+00:00
-- url     : https://prove2.me/submissions/0e64cb91-6702-4c4e-b2d9-dd0f447d9a47

import Mathlib
import Definitions.Def_OAIQ254M010
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkLog_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_finSumBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_CompactCertificate_entropyLookup_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_4_1I1R0Mass_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_4_1I1R0Raw_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_4_1I1R10H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_4_1I1R11P_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_4_1I1R12H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_4_1I1R13H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_4_1I1R14H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_4_1I1R15H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_4_1I1R16H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_4_1I1R1MassTerm_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_4_1I1R1Terms_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_4_1I1R2Entropy_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_4_1I1R2MassTerm_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_4_1I1R3Raw_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_4_1I1R4H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_4_1I1R5MassTerm_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_4_1I1R5Raw_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_4_1I1R6Mass_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_4_1I1R6Raw_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_4_1I1R7H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_4_1I1R8H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_4_1I1R9H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_entropyTerm_ball
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_homogeneous_enclosed

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_CertificatesReplay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.AllFieldCertificates

open MatrixMultiplication.Foundation.RationalLogCertificate

namespace Ball

theorem bounds {b : Ball} {x : ℝ} (h : b.Encloses x) :
    (b.lower : ℝ) ≤ x ∧ x ≤ (b.upper : ℝ) := by
  obtain ⟨hl, hu⟩ := abs_le.mp h
  simp only [lower, upper, Rat.cast_sub, Rat.cast_add]
  constructor <;> linarith

end Ball

end MatrixMultiplication.AllFieldCertificates

end

end MatrixAllFields

end OAI
end

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
open AllFieldInitialEntropyCertificate
open scoped BigOperators

lemma entropyTerm_zero_ball {p : ℝ} (hp : (Ball.exact 0).Encloses p) :
    (Ball.exact 0).Encloses (Foundation.entropyTerm p) := by
  have hb := Ball.bounds hp
  have h : p = 0 := by norm_num [Ball.lower, Ball.upper, Ball.exact] at hb <;> linarith
  simp only [h, Foundation.entropyTerm, neg_zero, zero_mul]
  simpa only [Rat.cast_zero] using Ball.exact_sound 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

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
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB3_4_1I1
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
lemma CB3_4_1I1R0Certificates_valid :
    CB3_4_1I1R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB3_4_1I1R0P_check : ∀ a : Fin 6, contains (CB3_4_1I1R0Raw a) (CB3_4_1I1R0P a) = true := by
  decide +kernel
lemma CB3_4_1I1R0P_sound (a : Fin 6) :
    (CB3_4_1I1R0P a).Encloses (CB3_4_1I1R0Value a) :=
  contains_sound (CB3_4_1I1R0Raw_sound a) (CB3_4_1I1R0P_check a)
lemma CB3_4_1I1R0Terms_sound (a : Fin 6) :
    (CB3_4_1I1R0Terms a).Encloses (Foundation.entropyTerm (CB3_4_1I1R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_4_1I1R0Certificates_valid
    (CB3_4_1I1R0CertificateIndex a) (CB3_4_1I1R0P_sound a)
lemma CB3_4_1I1R0Entropy_sound : CB3_4_1I1R0Entropy.Encloses (Foundation.finiteEntropy CB3_4_1I1R0Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_4_1I1R0Value CB3_4_1I1R0Terms CB3_4_1I1R0Terms_sound) (by decide +kernel)
lemma CB3_4_1I1R0MassTermLog_sound : CB3_4_1I1R0MassTermLog.Encloses (Real.log ((∑ a, CB3_4_1I1R0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB3_4_1I1R0Mass_sound) (w := CB3_4_1I1R0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CB3_4_1I1R0MassTerm_sound : CB3_4_1I1R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_4_1I1R0Value a))) := by
  exact contains_sound (entropyTerm_ball (CB3_4_1I1R0Mass_sound) CB3_4_1I1R0MassTermLog_sound) (by decide +kernel)
lemma CB3_4_1I1R0H_sound : CB3_4_1I1R0H.Encloses (homogeneousEntropy CB3_4_1I1R0Value) := by
  exact contains_sound (homogeneous_enclosed CB3_4_1I1R0Value CB3_4_1I1R0MassTerm_sound CB3_4_1I1R0Entropy_sound) (by decide +kernel)
lemma CB3_4_1I1R1Entropy_sound : CB3_4_1I1R1Entropy.Encloses (Foundation.finiteEntropy CB3_4_1I1R1Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_4_1I1R1Value CB3_4_1I1R1Terms CB3_4_1I1R1Terms_sound) (by decide +kernel)
lemma CB3_4_1I1R1H_sound : CB3_4_1I1R1H.Encloses (homogeneousEntropy CB3_4_1I1R1Value) := by
  exact contains_sound (homogeneous_enclosed CB3_4_1I1R1Value CB3_4_1I1R1MassTerm_sound CB3_4_1I1R1Entropy_sound) (by decide +kernel)
lemma CB3_4_1I1R2H_sound : CB3_4_1I1R2H.Encloses (homogeneousEntropy CB3_4_1I1R2Value) := by
  exact contains_sound (homogeneous_enclosed CB3_4_1I1R2Value CB3_4_1I1R2MassTerm_sound CB3_4_1I1R2Entropy_sound) (by decide +kernel)
lemma CB3_4_1I1R3Certificates_valid :
    CB3_4_1I1R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB3_4_1I1R3P_check : ∀ a : Fin 6, contains (CB3_4_1I1R3Raw a) (CB3_4_1I1R3P a) = true := by
  decide +kernel
lemma CB3_4_1I1R3P_sound (a : Fin 6) :
    (CB3_4_1I1R3P a).Encloses (CB3_4_1I1R3Value a) :=
  contains_sound (CB3_4_1I1R3Raw_sound a) (CB3_4_1I1R3P_check a)
lemma CB3_4_1I1R3Terms_sound (a : Fin 6) :
    (CB3_4_1I1R3Terms a).Encloses (Foundation.entropyTerm (CB3_4_1I1R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_4_1I1R3Certificates_valid
    (CB3_4_1I1R3CertificateIndex a) (CB3_4_1I1R3P_sound a)
lemma CB3_4_1I1R3Entropy_sound : CB3_4_1I1R3Entropy.Encloses (Foundation.finiteEntropy CB3_4_1I1R3Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_4_1I1R3Value CB3_4_1I1R3Terms CB3_4_1I1R3Terms_sound) (by decide +kernel)
lemma CB3_4_1I1R3Mass_sound : CB3_4_1I1R3Mass.Encloses (∑ a, CB3_4_1I1R3Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_4_1I1R3P CB3_4_1I1R3Value CB3_4_1I1R3P_sound) (by decide +kernel)
lemma CB3_4_1I1R3MassTermLog_sound : CB3_4_1I1R3MassTermLog.Encloses (Real.log ((∑ a, CB3_4_1I1R3Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB3_4_1I1R3Mass_sound) (w := CB3_4_1I1R3MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CB3_4_1I1R3MassTerm_sound : CB3_4_1I1R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_4_1I1R3Value a))) := by
  exact contains_sound (entropyTerm_ball (CB3_4_1I1R3Mass_sound) CB3_4_1I1R3MassTermLog_sound) (by decide +kernel)
lemma CB3_4_1I1R3H_sound : CB3_4_1I1R3H.Encloses (homogeneousEntropy CB3_4_1I1R3Value) := by
  exact contains_sound (homogeneous_enclosed CB3_4_1I1R3Value CB3_4_1I1R3MassTerm_sound CB3_4_1I1R3Entropy_sound) (by decide +kernel)
lemma CB3_4_1I1R5Certificates_valid :
    CB3_4_1I1R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB3_4_1I1R5P_check : ∀ a : Fin 6, contains (CB3_4_1I1R5Raw a) (CB3_4_1I1R5P a) = true := by
  decide +kernel
lemma CB3_4_1I1R5P_sound (a : Fin 6) :
    (CB3_4_1I1R5P a).Encloses (CB3_4_1I1R5Value a) :=
  contains_sound (CB3_4_1I1R5Raw_sound a) (CB3_4_1I1R5P_check a)
lemma CB3_4_1I1R5Terms_sound (a : Fin 6) :
    (CB3_4_1I1R5Terms a).Encloses (Foundation.entropyTerm (CB3_4_1I1R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_4_1I1R5Certificates_valid
    (CB3_4_1I1R5CertificateIndex a) (CB3_4_1I1R5P_sound a)
lemma CB3_4_1I1R5Entropy_sound : CB3_4_1I1R5Entropy.Encloses (Foundation.finiteEntropy CB3_4_1I1R5Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_4_1I1R5Value CB3_4_1I1R5Terms CB3_4_1I1R5Terms_sound) (by decide +kernel)
lemma CB3_4_1I1R5H_sound : CB3_4_1I1R5H.Encloses (homogeneousEntropy CB3_4_1I1R5Value) := by
  exact contains_sound (homogeneous_enclosed CB3_4_1I1R5Value CB3_4_1I1R5MassTerm_sound CB3_4_1I1R5Entropy_sound) (by decide +kernel)
lemma CB3_4_1I1R6Certificates_valid :
    CB3_4_1I1R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB3_4_1I1R6P_check : ∀ a : Fin 6, contains (CB3_4_1I1R6Raw a) (CB3_4_1I1R6P a) = true := by
  decide +kernel
lemma CB3_4_1I1R6P_sound (a : Fin 6) :
    (CB3_4_1I1R6P a).Encloses (CB3_4_1I1R6Value a) :=
  contains_sound (CB3_4_1I1R6Raw_sound a) (CB3_4_1I1R6P_check a)
lemma CB3_4_1I1R6Terms_sound (a : Fin 6) :
    (CB3_4_1I1R6Terms a).Encloses (Foundation.entropyTerm (CB3_4_1I1R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_4_1I1R6Certificates_valid
    (CB3_4_1I1R6CertificateIndex a) (CB3_4_1I1R6P_sound a)
lemma CB3_4_1I1R6Entropy_sound : CB3_4_1I1R6Entropy.Encloses (Foundation.finiteEntropy CB3_4_1I1R6Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_4_1I1R6Value CB3_4_1I1R6Terms CB3_4_1I1R6Terms_sound) (by decide +kernel)
lemma CB3_4_1I1R6MassTerm_sound : CB3_4_1I1R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_4_1I1R6Value a))) :=
  entropyTerm_zero_ball (CB3_4_1I1R6Mass_sound)
lemma CB3_4_1I1R6H_sound : CB3_4_1I1R6H.Encloses (homogeneousEntropy CB3_4_1I1R6Value) := by
  exact contains_sound (homogeneous_enclosed CB3_4_1I1R6Value CB3_4_1I1R6MassTerm_sound CB3_4_1I1R6Entropy_sound) (by decide +kernel)
lemma CB3_4_1I1R11Certificates_valid :
    CB3_4_1I1R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB3_4_1I1R11Terms_sound (a : Fin 6) :
    (CB3_4_1I1R11Terms a).Encloses (Foundation.entropyTerm (CB3_4_1I1R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_4_1I1R11Certificates_valid
    (CB3_4_1I1R11CertificateIndex a) (CB3_4_1I1R11P_sound a)
lemma CB3_4_1I1R11Entropy_sound : CB3_4_1I1R11Entropy.Encloses (Foundation.finiteEntropy CB3_4_1I1R11Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_4_1I1R11Value CB3_4_1I1R11Terms CB3_4_1I1R11Terms_sound) (by decide +kernel)
lemma CB3_4_1I1R11Mass_sound : CB3_4_1I1R11Mass.Encloses (∑ a, CB3_4_1I1R11Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_4_1I1R11P CB3_4_1I1R11Value CB3_4_1I1R11P_sound) (by decide +kernel)
lemma CB3_4_1I1R11MassTerm_sound : CB3_4_1I1R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_4_1I1R11Value a))) :=
  entropyTerm_zero_ball (CB3_4_1I1R11Mass_sound)
lemma CB3_4_1I1R11H_sound : CB3_4_1I1R11H.Encloses (homogeneousEntropy CB3_4_1I1R11Value) := by
  exact contains_sound (homogeneous_enclosed CB3_4_1I1R11Value CB3_4_1I1R11MassTerm_sound CB3_4_1I1R11Entropy_sound) (by decide +kernel)
lemma CB3_4_1I1ResidualEntropies_sound_oai (k : Fin 17) :
    (CB3_4_1I1ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 1 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 1) a : ℝ)) k)) := by
  fin_cases k
  · exact CB3_4_1I1R0H_sound
  · exact CB3_4_1I1R1H_sound
  · exact CB3_4_1I1R2H_sound
  · exact CB3_4_1I1R3H_sound
  · exact CB3_4_1I1R4H_sound
  · exact CB3_4_1I1R5H_sound
  · exact CB3_4_1I1R6H_sound
  · exact CB3_4_1I1R7H_sound
  · exact CB3_4_1I1R8H_sound
  · exact CB3_4_1I1R9H_sound
  · exact CB3_4_1I1R10H_sound
  · exact CB3_4_1I1R11H_sound
  · exact CB3_4_1I1R12H_sound
  · exact CB3_4_1I1R13H_sound
  · exact CB3_4_1I1R14H_sound
  · exact CB3_4_1I1R15H_sound
  · exact CB3_4_1I1R16H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_4_1I1ResidualEntropies_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_4_1I1ResidualEntropies_sound_oai
