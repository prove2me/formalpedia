-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I2ResidualEntropies_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T14:31:24.557143+00:00
-- url     : https://prove2.me/submissions/b33f77bf-cfef-4703-b4fa-ab9a0438b8b8

import Mathlib
import Definitions.Def_OAIQ254M010
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_finSumBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_CompactCertificate_entropyLookup_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_3_2I2R0H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_3_2I2R10H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_3_2I2R11H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_3_2I2R12H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_3_2I2R13H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_3_2I2R14H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_3_2I2R15H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_3_2I2R16H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_3_2I2R1MassTerm_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_3_2I2R1Raw_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_3_2I2R2MassTermLog_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_3_2I2R2Mass_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_3_2I2R2Raw_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_3_2I2R3H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_3_2I2R4MassTerm_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_3_2I2R4Raw_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_3_2I2R5Raw_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_3_2I2R6Raw_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_3_2I2R7Raw_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_3_2I2R8Raw_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_3_2I2R9Raw_sound
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
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB3_3_2I2
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
lemma CB3_3_2I2R1Certificates_valid :
    CB3_3_2I2R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB3_3_2I2R1P_check : ∀ a : Fin 6, contains (CB3_3_2I2R1Raw a) (CB3_3_2I2R1P a) = true := by
  decide +kernel
lemma CB3_3_2I2R1P_sound (a : Fin 6) :
    (CB3_3_2I2R1P a).Encloses (CB3_3_2I2R1Value a) :=
  contains_sound (CB3_3_2I2R1Raw_sound a) (CB3_3_2I2R1P_check a)
lemma CB3_3_2I2R1Terms_sound (a : Fin 6) :
    (CB3_3_2I2R1Terms a).Encloses (Foundation.entropyTerm (CB3_3_2I2R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_3_2I2R1Certificates_valid
    (CB3_3_2I2R1CertificateIndex a) (CB3_3_2I2R1P_sound a)
lemma CB3_3_2I2R1Entropy_sound : CB3_3_2I2R1Entropy.Encloses (Foundation.finiteEntropy CB3_3_2I2R1Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_3_2I2R1Value CB3_3_2I2R1Terms CB3_3_2I2R1Terms_sound) (by decide +kernel)
lemma CB3_3_2I2R1H_sound : CB3_3_2I2R1H.Encloses (homogeneousEntropy CB3_3_2I2R1Value) := by
  exact contains_sound (homogeneous_enclosed CB3_3_2I2R1Value CB3_3_2I2R1MassTerm_sound CB3_3_2I2R1Entropy_sound) (by decide +kernel)
lemma CB3_3_2I2R2Certificates_valid :
    CB3_3_2I2R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB3_3_2I2R2P_check : ∀ a : Fin 6, contains (CB3_3_2I2R2Raw a) (CB3_3_2I2R2P a) = true := by
  decide +kernel
lemma CB3_3_2I2R2P_sound (a : Fin 6) :
    (CB3_3_2I2R2P a).Encloses (CB3_3_2I2R2Value a) :=
  contains_sound (CB3_3_2I2R2Raw_sound a) (CB3_3_2I2R2P_check a)
lemma CB3_3_2I2R2Terms_sound (a : Fin 6) :
    (CB3_3_2I2R2Terms a).Encloses (Foundation.entropyTerm (CB3_3_2I2R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_3_2I2R2Certificates_valid
    (CB3_3_2I2R2CertificateIndex a) (CB3_3_2I2R2P_sound a)
lemma CB3_3_2I2R2Entropy_sound : CB3_3_2I2R2Entropy.Encloses (Foundation.finiteEntropy CB3_3_2I2R2Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_3_2I2R2Value CB3_3_2I2R2Terms CB3_3_2I2R2Terms_sound) (by decide +kernel)
lemma CB3_3_2I2R2MassTerm_sound : CB3_3_2I2R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_3_2I2R2Value a))) := by
  exact contains_sound (entropyTerm_ball (CB3_3_2I2R2Mass_sound) CB3_3_2I2R2MassTermLog_sound) (by decide +kernel)
lemma CB3_3_2I2R2H_sound : CB3_3_2I2R2H.Encloses (homogeneousEntropy CB3_3_2I2R2Value) := by
  exact contains_sound (homogeneous_enclosed CB3_3_2I2R2Value CB3_3_2I2R2MassTerm_sound CB3_3_2I2R2Entropy_sound) (by decide +kernel)
lemma CB3_3_2I2R4Certificates_valid :
    CB3_3_2I2R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB3_3_2I2R4P_check : ∀ a : Fin 6, contains (CB3_3_2I2R4Raw a) (CB3_3_2I2R4P a) = true := by
  decide +kernel
lemma CB3_3_2I2R4P_sound (a : Fin 6) :
    (CB3_3_2I2R4P a).Encloses (CB3_3_2I2R4Value a) :=
  contains_sound (CB3_3_2I2R4Raw_sound a) (CB3_3_2I2R4P_check a)
lemma CB3_3_2I2R4Terms_sound (a : Fin 6) :
    (CB3_3_2I2R4Terms a).Encloses (Foundation.entropyTerm (CB3_3_2I2R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_3_2I2R4Certificates_valid
    (CB3_3_2I2R4CertificateIndex a) (CB3_3_2I2R4P_sound a)
lemma CB3_3_2I2R4Entropy_sound : CB3_3_2I2R4Entropy.Encloses (Foundation.finiteEntropy CB3_3_2I2R4Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_3_2I2R4Value CB3_3_2I2R4Terms CB3_3_2I2R4Terms_sound) (by decide +kernel)
lemma CB3_3_2I2R4H_sound : CB3_3_2I2R4H.Encloses (homogeneousEntropy CB3_3_2I2R4Value) := by
  exact contains_sound (homogeneous_enclosed CB3_3_2I2R4Value CB3_3_2I2R4MassTerm_sound CB3_3_2I2R4Entropy_sound) (by decide +kernel)
lemma CB3_3_2I2R5Certificates_valid :
    CB3_3_2I2R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB3_3_2I2R5P_check : ∀ a : Fin 6, contains (CB3_3_2I2R5Raw a) (CB3_3_2I2R5P a) = true := by
  decide +kernel
lemma CB3_3_2I2R5P_sound (a : Fin 6) :
    (CB3_3_2I2R5P a).Encloses (CB3_3_2I2R5Value a) :=
  contains_sound (CB3_3_2I2R5Raw_sound a) (CB3_3_2I2R5P_check a)
lemma CB3_3_2I2R5Terms_sound (a : Fin 6) :
    (CB3_3_2I2R5Terms a).Encloses (Foundation.entropyTerm (CB3_3_2I2R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_3_2I2R5Certificates_valid
    (CB3_3_2I2R5CertificateIndex a) (CB3_3_2I2R5P_sound a)
lemma CB3_3_2I2R5Entropy_sound : CB3_3_2I2R5Entropy.Encloses (Foundation.finiteEntropy CB3_3_2I2R5Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_3_2I2R5Value CB3_3_2I2R5Terms CB3_3_2I2R5Terms_sound) (by decide +kernel)
lemma CB3_3_2I2R5Mass_sound : CB3_3_2I2R5Mass.Encloses (∑ a, CB3_3_2I2R5Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_3_2I2R5P CB3_3_2I2R5Value CB3_3_2I2R5P_sound) (by decide +kernel)
lemma CB3_3_2I2R5MassTerm_sound : CB3_3_2I2R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_3_2I2R5Value a))) :=
  entropyTerm_zero_ball (CB3_3_2I2R5Mass_sound)
lemma CB3_3_2I2R5H_sound : CB3_3_2I2R5H.Encloses (homogeneousEntropy CB3_3_2I2R5Value) := by
  exact contains_sound (homogeneous_enclosed CB3_3_2I2R5Value CB3_3_2I2R5MassTerm_sound CB3_3_2I2R5Entropy_sound) (by decide +kernel)
lemma CB3_3_2I2R6Certificates_valid :
    CB3_3_2I2R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB3_3_2I2R6P_check : ∀ a : Fin 6, contains (CB3_3_2I2R6Raw a) (CB3_3_2I2R6P a) = true := by
  decide +kernel
lemma CB3_3_2I2R6P_sound (a : Fin 6) :
    (CB3_3_2I2R6P a).Encloses (CB3_3_2I2R6Value a) :=
  contains_sound (CB3_3_2I2R6Raw_sound a) (CB3_3_2I2R6P_check a)
lemma CB3_3_2I2R6Terms_sound (a : Fin 6) :
    (CB3_3_2I2R6Terms a).Encloses (Foundation.entropyTerm (CB3_3_2I2R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_3_2I2R6Certificates_valid
    (CB3_3_2I2R6CertificateIndex a) (CB3_3_2I2R6P_sound a)
lemma CB3_3_2I2R6Entropy_sound : CB3_3_2I2R6Entropy.Encloses (Foundation.finiteEntropy CB3_3_2I2R6Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_3_2I2R6Value CB3_3_2I2R6Terms CB3_3_2I2R6Terms_sound) (by decide +kernel)
lemma CB3_3_2I2R6Mass_sound : CB3_3_2I2R6Mass.Encloses (∑ a, CB3_3_2I2R6Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_3_2I2R6P CB3_3_2I2R6Value CB3_3_2I2R6P_sound) (by decide +kernel)
lemma CB3_3_2I2R6MassTerm_sound : CB3_3_2I2R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_3_2I2R6Value a))) :=
  entropyTerm_zero_ball (CB3_3_2I2R6Mass_sound)
lemma CB3_3_2I2R6H_sound : CB3_3_2I2R6H.Encloses (homogeneousEntropy CB3_3_2I2R6Value) := by
  exact contains_sound (homogeneous_enclosed CB3_3_2I2R6Value CB3_3_2I2R6MassTerm_sound CB3_3_2I2R6Entropy_sound) (by decide +kernel)
lemma CB3_3_2I2R7Certificates_valid :
    CB3_3_2I2R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB3_3_2I2R7P_check : ∀ a : Fin 6, contains (CB3_3_2I2R7Raw a) (CB3_3_2I2R7P a) = true := by
  decide +kernel
lemma CB3_3_2I2R7P_sound (a : Fin 6) :
    (CB3_3_2I2R7P a).Encloses (CB3_3_2I2R7Value a) :=
  contains_sound (CB3_3_2I2R7Raw_sound a) (CB3_3_2I2R7P_check a)
lemma CB3_3_2I2R7Terms_sound (a : Fin 6) :
    (CB3_3_2I2R7Terms a).Encloses (Foundation.entropyTerm (CB3_3_2I2R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_3_2I2R7Certificates_valid
    (CB3_3_2I2R7CertificateIndex a) (CB3_3_2I2R7P_sound a)
lemma CB3_3_2I2R7Entropy_sound : CB3_3_2I2R7Entropy.Encloses (Foundation.finiteEntropy CB3_3_2I2R7Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_3_2I2R7Value CB3_3_2I2R7Terms CB3_3_2I2R7Terms_sound) (by decide +kernel)
lemma CB3_3_2I2R7Mass_sound : CB3_3_2I2R7Mass.Encloses (∑ a, CB3_3_2I2R7Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_3_2I2R7P CB3_3_2I2R7Value CB3_3_2I2R7P_sound) (by decide +kernel)
lemma CB3_3_2I2R7MassTerm_sound : CB3_3_2I2R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_3_2I2R7Value a))) :=
  entropyTerm_zero_ball (CB3_3_2I2R7Mass_sound)
lemma CB3_3_2I2R7H_sound : CB3_3_2I2R7H.Encloses (homogeneousEntropy CB3_3_2I2R7Value) := by
  exact contains_sound (homogeneous_enclosed CB3_3_2I2R7Value CB3_3_2I2R7MassTerm_sound CB3_3_2I2R7Entropy_sound) (by decide +kernel)
lemma CB3_3_2I2R8Certificates_valid :
    CB3_3_2I2R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB3_3_2I2R8P_check : ∀ a : Fin 6, contains (CB3_3_2I2R8Raw a) (CB3_3_2I2R8P a) = true := by
  decide +kernel
lemma CB3_3_2I2R8P_sound (a : Fin 6) :
    (CB3_3_2I2R8P a).Encloses (CB3_3_2I2R8Value a) :=
  contains_sound (CB3_3_2I2R8Raw_sound a) (CB3_3_2I2R8P_check a)
lemma CB3_3_2I2R8Terms_sound (a : Fin 6) :
    (CB3_3_2I2R8Terms a).Encloses (Foundation.entropyTerm (CB3_3_2I2R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_3_2I2R8Certificates_valid
    (CB3_3_2I2R8CertificateIndex a) (CB3_3_2I2R8P_sound a)
lemma CB3_3_2I2R8Entropy_sound : CB3_3_2I2R8Entropy.Encloses (Foundation.finiteEntropy CB3_3_2I2R8Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_3_2I2R8Value CB3_3_2I2R8Terms CB3_3_2I2R8Terms_sound) (by decide +kernel)
lemma CB3_3_2I2R8Mass_sound : CB3_3_2I2R8Mass.Encloses (∑ a, CB3_3_2I2R8Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_3_2I2R8P CB3_3_2I2R8Value CB3_3_2I2R8P_sound) (by decide +kernel)
lemma CB3_3_2I2R8MassTerm_sound : CB3_3_2I2R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_3_2I2R8Value a))) :=
  entropyTerm_zero_ball (CB3_3_2I2R8Mass_sound)
lemma CB3_3_2I2R8H_sound : CB3_3_2I2R8H.Encloses (homogeneousEntropy CB3_3_2I2R8Value) := by
  exact contains_sound (homogeneous_enclosed CB3_3_2I2R8Value CB3_3_2I2R8MassTerm_sound CB3_3_2I2R8Entropy_sound) (by decide +kernel)
lemma CB3_3_2I2R9Certificates_valid :
    CB3_3_2I2R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB3_3_2I2R9P_check : ∀ a : Fin 6, contains (CB3_3_2I2R9Raw a) (CB3_3_2I2R9P a) = true := by
  decide +kernel
lemma CB3_3_2I2R9P_sound (a : Fin 6) :
    (CB3_3_2I2R9P a).Encloses (CB3_3_2I2R9Value a) :=
  contains_sound (CB3_3_2I2R9Raw_sound a) (CB3_3_2I2R9P_check a)
lemma CB3_3_2I2R9Terms_sound (a : Fin 6) :
    (CB3_3_2I2R9Terms a).Encloses (Foundation.entropyTerm (CB3_3_2I2R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_3_2I2R9Certificates_valid
    (CB3_3_2I2R9CertificateIndex a) (CB3_3_2I2R9P_sound a)
lemma CB3_3_2I2R9Entropy_sound : CB3_3_2I2R9Entropy.Encloses (Foundation.finiteEntropy CB3_3_2I2R9Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_3_2I2R9Value CB3_3_2I2R9Terms CB3_3_2I2R9Terms_sound) (by decide +kernel)
lemma CB3_3_2I2R9Mass_sound : CB3_3_2I2R9Mass.Encloses (∑ a, CB3_3_2I2R9Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_3_2I2R9P CB3_3_2I2R9Value CB3_3_2I2R9P_sound) (by decide +kernel)
lemma CB3_3_2I2R9MassTerm_sound : CB3_3_2I2R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_3_2I2R9Value a))) :=
  entropyTerm_zero_ball (CB3_3_2I2R9Mass_sound)
lemma CB3_3_2I2R9H_sound : CB3_3_2I2R9H.Encloses (homogeneousEntropy CB3_3_2I2R9Value) := by
  exact contains_sound (homogeneous_enclosed CB3_3_2I2R9Value CB3_3_2I2R9MassTerm_sound CB3_3_2I2R9Entropy_sound) (by decide +kernel)
lemma CB3_3_2I2ResidualEntropies_sound_oai (k : Fin 17) :
    (CB3_3_2I2ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 3 3 2)) (fun u => (stageBLaw (shape 3 3 2) u : ℝ)) (stageBPriority (shape 3 3 2)) 2 (fun u a => (littleLaw (shape 3 3 2) u ((stageBPriority (shape 3 3 2)) 2) a : ℝ)) k)) := by
  fin_cases k
  · exact CB3_3_2I2R0H_sound
  · exact CB3_3_2I2R1H_sound
  · exact CB3_3_2I2R2H_sound
  · exact CB3_3_2I2R3H_sound
  · exact CB3_3_2I2R4H_sound
  · exact CB3_3_2I2R5H_sound
  · exact CB3_3_2I2R6H_sound
  · exact CB3_3_2I2R7H_sound
  · exact CB3_3_2I2R8H_sound
  · exact CB3_3_2I2R9H_sound
  · exact CB3_3_2I2R10H_sound
  · exact CB3_3_2I2R11H_sound
  · exact CB3_3_2I2R12H_sound
  · exact CB3_3_2I2R13H_sound
  · exact CB3_3_2I2R14H_sound
  · exact CB3_3_2I2R15H_sound
  · exact CB3_3_2I2R16H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I2ResidualEntropies_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I2ResidualEntropies_sound_oai
