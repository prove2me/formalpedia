-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB1_6_1I2ResidualEntropies_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T13:14:47.590735+00:00
-- url     : https://prove2.me/submissions/fe7a244e-89f5-4648-b28a-5eb424e38226

import Mathlib
import Definitions.Def_OAIQ254M010
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_finSumBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_CompactCertificate_entropyLookup_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB1_6_1I2R0MassTerm_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB1_6_1I2R0Terms_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB1_6_1I2R10Entropy_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB1_6_1I2R10Mass_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB1_6_1I2R11Raw_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB1_6_1I2R12Raw_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB1_6_1I2R13Raw_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB1_6_1I2R14Raw_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB1_6_1I2R15Raw_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB1_6_1I2R16Raw_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB1_6_1I2R1H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB1_6_1I2R2H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB1_6_1I2R3MassTerm_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB1_6_1I2R3Terms_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB1_6_1I2R4P_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB1_6_1I2R5Raw_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB1_6_1I2R6Raw_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB1_6_1I2R7Raw_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB1_6_1I2R8Raw_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB1_6_1I2R9Raw_sound
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
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB1_6_1I2
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
lemma CB1_6_1I2R0Entropy_sound : CB1_6_1I2R0Entropy.Encloses (Foundation.finiteEntropy CB1_6_1I2R0Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_6_1I2R0Value CB1_6_1I2R0Terms CB1_6_1I2R0Terms_sound) (by decide +kernel)
lemma CB1_6_1I2R0H_sound : CB1_6_1I2R0H.Encloses (homogeneousEntropy CB1_6_1I2R0Value) := by
  exact contains_sound (homogeneous_enclosed CB1_6_1I2R0Value CB1_6_1I2R0MassTerm_sound CB1_6_1I2R0Entropy_sound) (by decide +kernel)
lemma CB1_6_1I2R3Entropy_sound : CB1_6_1I2R3Entropy.Encloses (Foundation.finiteEntropy CB1_6_1I2R3Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_6_1I2R3Value CB1_6_1I2R3Terms CB1_6_1I2R3Terms_sound) (by decide +kernel)
lemma CB1_6_1I2R3H_sound : CB1_6_1I2R3H.Encloses (homogeneousEntropy CB1_6_1I2R3Value) := by
  exact contains_sound (homogeneous_enclosed CB1_6_1I2R3Value CB1_6_1I2R3MassTerm_sound CB1_6_1I2R3Entropy_sound) (by decide +kernel)
lemma CB1_6_1I2R4Certificates_valid :
    CB1_6_1I2R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB1_6_1I2R4Terms_sound (a : Fin 6) :
    (CB1_6_1I2R4Terms a).Encloses (Foundation.entropyTerm (CB1_6_1I2R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_6_1I2R4Certificates_valid
    (CB1_6_1I2R4CertificateIndex a) (CB1_6_1I2R4P_sound a)
lemma CB1_6_1I2R4Entropy_sound : CB1_6_1I2R4Entropy.Encloses (Foundation.finiteEntropy CB1_6_1I2R4Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_6_1I2R4Value CB1_6_1I2R4Terms CB1_6_1I2R4Terms_sound) (by decide +kernel)
lemma CB1_6_1I2R4Mass_sound : CB1_6_1I2R4Mass.Encloses (∑ a, CB1_6_1I2R4Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_6_1I2R4P CB1_6_1I2R4Value CB1_6_1I2R4P_sound) (by decide +kernel)
lemma CB1_6_1I2R4MassTerm_sound : CB1_6_1I2R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_6_1I2R4Value a))) :=
  entropyTerm_zero_ball (CB1_6_1I2R4Mass_sound)
lemma CB1_6_1I2R4H_sound : CB1_6_1I2R4H.Encloses (homogeneousEntropy CB1_6_1I2R4Value) := by
  exact contains_sound (homogeneous_enclosed CB1_6_1I2R4Value CB1_6_1I2R4MassTerm_sound CB1_6_1I2R4Entropy_sound) (by decide +kernel)
lemma CB1_6_1I2R5Certificates_valid :
    CB1_6_1I2R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB1_6_1I2R5P_check : ∀ a : Fin 6, contains (CB1_6_1I2R5Raw a) (CB1_6_1I2R5P a) = true := by
  decide +kernel
lemma CB1_6_1I2R5P_sound (a : Fin 6) :
    (CB1_6_1I2R5P a).Encloses (CB1_6_1I2R5Value a) :=
  contains_sound (CB1_6_1I2R5Raw_sound a) (CB1_6_1I2R5P_check a)
lemma CB1_6_1I2R5Terms_sound (a : Fin 6) :
    (CB1_6_1I2R5Terms a).Encloses (Foundation.entropyTerm (CB1_6_1I2R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_6_1I2R5Certificates_valid
    (CB1_6_1I2R5CertificateIndex a) (CB1_6_1I2R5P_sound a)
lemma CB1_6_1I2R5Entropy_sound : CB1_6_1I2R5Entropy.Encloses (Foundation.finiteEntropy CB1_6_1I2R5Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_6_1I2R5Value CB1_6_1I2R5Terms CB1_6_1I2R5Terms_sound) (by decide +kernel)
lemma CB1_6_1I2R5Mass_sound : CB1_6_1I2R5Mass.Encloses (∑ a, CB1_6_1I2R5Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_6_1I2R5P CB1_6_1I2R5Value CB1_6_1I2R5P_sound) (by decide +kernel)
lemma CB1_6_1I2R5MassTerm_sound : CB1_6_1I2R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_6_1I2R5Value a))) :=
  entropyTerm_zero_ball (CB1_6_1I2R5Mass_sound)
lemma CB1_6_1I2R5H_sound : CB1_6_1I2R5H.Encloses (homogeneousEntropy CB1_6_1I2R5Value) := by
  exact contains_sound (homogeneous_enclosed CB1_6_1I2R5Value CB1_6_1I2R5MassTerm_sound CB1_6_1I2R5Entropy_sound) (by decide +kernel)
lemma CB1_6_1I2R6Certificates_valid :
    CB1_6_1I2R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB1_6_1I2R6P_check : ∀ a : Fin 6, contains (CB1_6_1I2R6Raw a) (CB1_6_1I2R6P a) = true := by
  decide +kernel
lemma CB1_6_1I2R6P_sound (a : Fin 6) :
    (CB1_6_1I2R6P a).Encloses (CB1_6_1I2R6Value a) :=
  contains_sound (CB1_6_1I2R6Raw_sound a) (CB1_6_1I2R6P_check a)
lemma CB1_6_1I2R6Terms_sound (a : Fin 6) :
    (CB1_6_1I2R6Terms a).Encloses (Foundation.entropyTerm (CB1_6_1I2R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_6_1I2R6Certificates_valid
    (CB1_6_1I2R6CertificateIndex a) (CB1_6_1I2R6P_sound a)
lemma CB1_6_1I2R6Entropy_sound : CB1_6_1I2R6Entropy.Encloses (Foundation.finiteEntropy CB1_6_1I2R6Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_6_1I2R6Value CB1_6_1I2R6Terms CB1_6_1I2R6Terms_sound) (by decide +kernel)
lemma CB1_6_1I2R6Mass_sound : CB1_6_1I2R6Mass.Encloses (∑ a, CB1_6_1I2R6Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_6_1I2R6P CB1_6_1I2R6Value CB1_6_1I2R6P_sound) (by decide +kernel)
lemma CB1_6_1I2R6MassTerm_sound : CB1_6_1I2R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_6_1I2R6Value a))) :=
  entropyTerm_zero_ball (CB1_6_1I2R6Mass_sound)
lemma CB1_6_1I2R6H_sound : CB1_6_1I2R6H.Encloses (homogeneousEntropy CB1_6_1I2R6Value) := by
  exact contains_sound (homogeneous_enclosed CB1_6_1I2R6Value CB1_6_1I2R6MassTerm_sound CB1_6_1I2R6Entropy_sound) (by decide +kernel)
lemma CB1_6_1I2R7Certificates_valid :
    CB1_6_1I2R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB1_6_1I2R7P_check : ∀ a : Fin 6, contains (CB1_6_1I2R7Raw a) (CB1_6_1I2R7P a) = true := by
  decide +kernel
lemma CB1_6_1I2R7P_sound (a : Fin 6) :
    (CB1_6_1I2R7P a).Encloses (CB1_6_1I2R7Value a) :=
  contains_sound (CB1_6_1I2R7Raw_sound a) (CB1_6_1I2R7P_check a)
lemma CB1_6_1I2R7Terms_sound (a : Fin 6) :
    (CB1_6_1I2R7Terms a).Encloses (Foundation.entropyTerm (CB1_6_1I2R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_6_1I2R7Certificates_valid
    (CB1_6_1I2R7CertificateIndex a) (CB1_6_1I2R7P_sound a)
lemma CB1_6_1I2R7Entropy_sound : CB1_6_1I2R7Entropy.Encloses (Foundation.finiteEntropy CB1_6_1I2R7Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_6_1I2R7Value CB1_6_1I2R7Terms CB1_6_1I2R7Terms_sound) (by decide +kernel)
lemma CB1_6_1I2R7Mass_sound : CB1_6_1I2R7Mass.Encloses (∑ a, CB1_6_1I2R7Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_6_1I2R7P CB1_6_1I2R7Value CB1_6_1I2R7P_sound) (by decide +kernel)
lemma CB1_6_1I2R7MassTerm_sound : CB1_6_1I2R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_6_1I2R7Value a))) :=
  entropyTerm_zero_ball (CB1_6_1I2R7Mass_sound)
lemma CB1_6_1I2R7H_sound : CB1_6_1I2R7H.Encloses (homogeneousEntropy CB1_6_1I2R7Value) := by
  exact contains_sound (homogeneous_enclosed CB1_6_1I2R7Value CB1_6_1I2R7MassTerm_sound CB1_6_1I2R7Entropy_sound) (by decide +kernel)
lemma CB1_6_1I2R8Certificates_valid :
    CB1_6_1I2R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB1_6_1I2R8P_check : ∀ a : Fin 6, contains (CB1_6_1I2R8Raw a) (CB1_6_1I2R8P a) = true := by
  decide +kernel
lemma CB1_6_1I2R8P_sound (a : Fin 6) :
    (CB1_6_1I2R8P a).Encloses (CB1_6_1I2R8Value a) :=
  contains_sound (CB1_6_1I2R8Raw_sound a) (CB1_6_1I2R8P_check a)
lemma CB1_6_1I2R8Terms_sound (a : Fin 6) :
    (CB1_6_1I2R8Terms a).Encloses (Foundation.entropyTerm (CB1_6_1I2R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_6_1I2R8Certificates_valid
    (CB1_6_1I2R8CertificateIndex a) (CB1_6_1I2R8P_sound a)
lemma CB1_6_1I2R8Entropy_sound : CB1_6_1I2R8Entropy.Encloses (Foundation.finiteEntropy CB1_6_1I2R8Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_6_1I2R8Value CB1_6_1I2R8Terms CB1_6_1I2R8Terms_sound) (by decide +kernel)
lemma CB1_6_1I2R8Mass_sound : CB1_6_1I2R8Mass.Encloses (∑ a, CB1_6_1I2R8Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_6_1I2R8P CB1_6_1I2R8Value CB1_6_1I2R8P_sound) (by decide +kernel)
lemma CB1_6_1I2R8MassTerm_sound : CB1_6_1I2R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_6_1I2R8Value a))) :=
  entropyTerm_zero_ball (CB1_6_1I2R8Mass_sound)
lemma CB1_6_1I2R8H_sound : CB1_6_1I2R8H.Encloses (homogeneousEntropy CB1_6_1I2R8Value) := by
  exact contains_sound (homogeneous_enclosed CB1_6_1I2R8Value CB1_6_1I2R8MassTerm_sound CB1_6_1I2R8Entropy_sound) (by decide +kernel)
lemma CB1_6_1I2R9Certificates_valid :
    CB1_6_1I2R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB1_6_1I2R9P_check : ∀ a : Fin 6, contains (CB1_6_1I2R9Raw a) (CB1_6_1I2R9P a) = true := by
  decide +kernel
lemma CB1_6_1I2R9P_sound (a : Fin 6) :
    (CB1_6_1I2R9P a).Encloses (CB1_6_1I2R9Value a) :=
  contains_sound (CB1_6_1I2R9Raw_sound a) (CB1_6_1I2R9P_check a)
lemma CB1_6_1I2R9Terms_sound (a : Fin 6) :
    (CB1_6_1I2R9Terms a).Encloses (Foundation.entropyTerm (CB1_6_1I2R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_6_1I2R9Certificates_valid
    (CB1_6_1I2R9CertificateIndex a) (CB1_6_1I2R9P_sound a)
lemma CB1_6_1I2R9Entropy_sound : CB1_6_1I2R9Entropy.Encloses (Foundation.finiteEntropy CB1_6_1I2R9Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_6_1I2R9Value CB1_6_1I2R9Terms CB1_6_1I2R9Terms_sound) (by decide +kernel)
lemma CB1_6_1I2R9Mass_sound : CB1_6_1I2R9Mass.Encloses (∑ a, CB1_6_1I2R9Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_6_1I2R9P CB1_6_1I2R9Value CB1_6_1I2R9P_sound) (by decide +kernel)
lemma CB1_6_1I2R9MassTerm_sound : CB1_6_1I2R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_6_1I2R9Value a))) :=
  entropyTerm_zero_ball (CB1_6_1I2R9Mass_sound)
lemma CB1_6_1I2R9H_sound : CB1_6_1I2R9H.Encloses (homogeneousEntropy CB1_6_1I2R9Value) := by
  exact contains_sound (homogeneous_enclosed CB1_6_1I2R9Value CB1_6_1I2R9MassTerm_sound CB1_6_1I2R9Entropy_sound) (by decide +kernel)
lemma CB1_6_1I2R10MassTerm_sound : CB1_6_1I2R10MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_6_1I2R10Value a))) :=
  entropyTerm_zero_ball (CB1_6_1I2R10Mass_sound)
lemma CB1_6_1I2R10H_sound : CB1_6_1I2R10H.Encloses (homogeneousEntropy CB1_6_1I2R10Value) := by
  exact contains_sound (homogeneous_enclosed CB1_6_1I2R10Value CB1_6_1I2R10MassTerm_sound CB1_6_1I2R10Entropy_sound) (by decide +kernel)
lemma CB1_6_1I2R11Certificates_valid :
    CB1_6_1I2R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB1_6_1I2R11P_check : ∀ a : Fin 6, contains (CB1_6_1I2R11Raw a) (CB1_6_1I2R11P a) = true := by
  decide +kernel
lemma CB1_6_1I2R11P_sound (a : Fin 6) :
    (CB1_6_1I2R11P a).Encloses (CB1_6_1I2R11Value a) :=
  contains_sound (CB1_6_1I2R11Raw_sound a) (CB1_6_1I2R11P_check a)
lemma CB1_6_1I2R11Terms_sound (a : Fin 6) :
    (CB1_6_1I2R11Terms a).Encloses (Foundation.entropyTerm (CB1_6_1I2R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_6_1I2R11Certificates_valid
    (CB1_6_1I2R11CertificateIndex a) (CB1_6_1I2R11P_sound a)
lemma CB1_6_1I2R11Entropy_sound : CB1_6_1I2R11Entropy.Encloses (Foundation.finiteEntropy CB1_6_1I2R11Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_6_1I2R11Value CB1_6_1I2R11Terms CB1_6_1I2R11Terms_sound) (by decide +kernel)
lemma CB1_6_1I2R11Mass_sound : CB1_6_1I2R11Mass.Encloses (∑ a, CB1_6_1I2R11Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_6_1I2R11P CB1_6_1I2R11Value CB1_6_1I2R11P_sound) (by decide +kernel)
lemma CB1_6_1I2R11MassTerm_sound : CB1_6_1I2R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_6_1I2R11Value a))) :=
  entropyTerm_zero_ball (CB1_6_1I2R11Mass_sound)
lemma CB1_6_1I2R11H_sound : CB1_6_1I2R11H.Encloses (homogeneousEntropy CB1_6_1I2R11Value) := by
  exact contains_sound (homogeneous_enclosed CB1_6_1I2R11Value CB1_6_1I2R11MassTerm_sound CB1_6_1I2R11Entropy_sound) (by decide +kernel)
lemma CB1_6_1I2R12Certificates_valid :
    CB1_6_1I2R12Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB1_6_1I2R12P_check : ∀ a : Fin 6, contains (CB1_6_1I2R12Raw a) (CB1_6_1I2R12P a) = true := by
  decide +kernel
lemma CB1_6_1I2R12P_sound (a : Fin 6) :
    (CB1_6_1I2R12P a).Encloses (CB1_6_1I2R12Value a) :=
  contains_sound (CB1_6_1I2R12Raw_sound a) (CB1_6_1I2R12P_check a)
lemma CB1_6_1I2R12Terms_sound (a : Fin 6) :
    (CB1_6_1I2R12Terms a).Encloses (Foundation.entropyTerm (CB1_6_1I2R12Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_6_1I2R12Certificates_valid
    (CB1_6_1I2R12CertificateIndex a) (CB1_6_1I2R12P_sound a)
lemma CB1_6_1I2R12Entropy_sound : CB1_6_1I2R12Entropy.Encloses (Foundation.finiteEntropy CB1_6_1I2R12Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_6_1I2R12Value CB1_6_1I2R12Terms CB1_6_1I2R12Terms_sound) (by decide +kernel)
lemma CB1_6_1I2R12Mass_sound : CB1_6_1I2R12Mass.Encloses (∑ a, CB1_6_1I2R12Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_6_1I2R12P CB1_6_1I2R12Value CB1_6_1I2R12P_sound) (by decide +kernel)
lemma CB1_6_1I2R12MassTerm_sound : CB1_6_1I2R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_6_1I2R12Value a))) :=
  entropyTerm_zero_ball (CB1_6_1I2R12Mass_sound)
lemma CB1_6_1I2R12H_sound : CB1_6_1I2R12H.Encloses (homogeneousEntropy CB1_6_1I2R12Value) := by
  exact contains_sound (homogeneous_enclosed CB1_6_1I2R12Value CB1_6_1I2R12MassTerm_sound CB1_6_1I2R12Entropy_sound) (by decide +kernel)
lemma CB1_6_1I2R13Certificates_valid :
    CB1_6_1I2R13Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB1_6_1I2R13P_check : ∀ a : Fin 6, contains (CB1_6_1I2R13Raw a) (CB1_6_1I2R13P a) = true := by
  decide +kernel
lemma CB1_6_1I2R13P_sound (a : Fin 6) :
    (CB1_6_1I2R13P a).Encloses (CB1_6_1I2R13Value a) :=
  contains_sound (CB1_6_1I2R13Raw_sound a) (CB1_6_1I2R13P_check a)
lemma CB1_6_1I2R13Terms_sound (a : Fin 6) :
    (CB1_6_1I2R13Terms a).Encloses (Foundation.entropyTerm (CB1_6_1I2R13Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_6_1I2R13Certificates_valid
    (CB1_6_1I2R13CertificateIndex a) (CB1_6_1I2R13P_sound a)
lemma CB1_6_1I2R13Entropy_sound : CB1_6_1I2R13Entropy.Encloses (Foundation.finiteEntropy CB1_6_1I2R13Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_6_1I2R13Value CB1_6_1I2R13Terms CB1_6_1I2R13Terms_sound) (by decide +kernel)
lemma CB1_6_1I2R13Mass_sound : CB1_6_1I2R13Mass.Encloses (∑ a, CB1_6_1I2R13Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_6_1I2R13P CB1_6_1I2R13Value CB1_6_1I2R13P_sound) (by decide +kernel)
lemma CB1_6_1I2R13MassTerm_sound : CB1_6_1I2R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_6_1I2R13Value a))) :=
  entropyTerm_zero_ball (CB1_6_1I2R13Mass_sound)
lemma CB1_6_1I2R13H_sound : CB1_6_1I2R13H.Encloses (homogeneousEntropy CB1_6_1I2R13Value) := by
  exact contains_sound (homogeneous_enclosed CB1_6_1I2R13Value CB1_6_1I2R13MassTerm_sound CB1_6_1I2R13Entropy_sound) (by decide +kernel)
lemma CB1_6_1I2R14Certificates_valid :
    CB1_6_1I2R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB1_6_1I2R14P_check : ∀ a : Fin 6, contains (CB1_6_1I2R14Raw a) (CB1_6_1I2R14P a) = true := by
  decide +kernel
lemma CB1_6_1I2R14P_sound (a : Fin 6) :
    (CB1_6_1I2R14P a).Encloses (CB1_6_1I2R14Value a) :=
  contains_sound (CB1_6_1I2R14Raw_sound a) (CB1_6_1I2R14P_check a)
lemma CB1_6_1I2R14Terms_sound (a : Fin 6) :
    (CB1_6_1I2R14Terms a).Encloses (Foundation.entropyTerm (CB1_6_1I2R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_6_1I2R14Certificates_valid
    (CB1_6_1I2R14CertificateIndex a) (CB1_6_1I2R14P_sound a)
lemma CB1_6_1I2R14Entropy_sound : CB1_6_1I2R14Entropy.Encloses (Foundation.finiteEntropy CB1_6_1I2R14Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_6_1I2R14Value CB1_6_1I2R14Terms CB1_6_1I2R14Terms_sound) (by decide +kernel)
lemma CB1_6_1I2R14Mass_sound : CB1_6_1I2R14Mass.Encloses (∑ a, CB1_6_1I2R14Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_6_1I2R14P CB1_6_1I2R14Value CB1_6_1I2R14P_sound) (by decide +kernel)
lemma CB1_6_1I2R14MassTerm_sound : CB1_6_1I2R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_6_1I2R14Value a))) :=
  entropyTerm_zero_ball (CB1_6_1I2R14Mass_sound)
lemma CB1_6_1I2R14H_sound : CB1_6_1I2R14H.Encloses (homogeneousEntropy CB1_6_1I2R14Value) := by
  exact contains_sound (homogeneous_enclosed CB1_6_1I2R14Value CB1_6_1I2R14MassTerm_sound CB1_6_1I2R14Entropy_sound) (by decide +kernel)
lemma CB1_6_1I2R15Certificates_valid :
    CB1_6_1I2R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB1_6_1I2R15P_check : ∀ a : Fin 6, contains (CB1_6_1I2R15Raw a) (CB1_6_1I2R15P a) = true := by
  decide +kernel
lemma CB1_6_1I2R15P_sound (a : Fin 6) :
    (CB1_6_1I2R15P a).Encloses (CB1_6_1I2R15Value a) :=
  contains_sound (CB1_6_1I2R15Raw_sound a) (CB1_6_1I2R15P_check a)
lemma CB1_6_1I2R15Terms_sound (a : Fin 6) :
    (CB1_6_1I2R15Terms a).Encloses (Foundation.entropyTerm (CB1_6_1I2R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_6_1I2R15Certificates_valid
    (CB1_6_1I2R15CertificateIndex a) (CB1_6_1I2R15P_sound a)
lemma CB1_6_1I2R15Entropy_sound : CB1_6_1I2R15Entropy.Encloses (Foundation.finiteEntropy CB1_6_1I2R15Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_6_1I2R15Value CB1_6_1I2R15Terms CB1_6_1I2R15Terms_sound) (by decide +kernel)
lemma CB1_6_1I2R15Mass_sound : CB1_6_1I2R15Mass.Encloses (∑ a, CB1_6_1I2R15Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_6_1I2R15P CB1_6_1I2R15Value CB1_6_1I2R15P_sound) (by decide +kernel)
lemma CB1_6_1I2R15MassTerm_sound : CB1_6_1I2R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_6_1I2R15Value a))) :=
  entropyTerm_zero_ball (CB1_6_1I2R15Mass_sound)
lemma CB1_6_1I2R15H_sound : CB1_6_1I2R15H.Encloses (homogeneousEntropy CB1_6_1I2R15Value) := by
  exact contains_sound (homogeneous_enclosed CB1_6_1I2R15Value CB1_6_1I2R15MassTerm_sound CB1_6_1I2R15Entropy_sound) (by decide +kernel)
lemma CB1_6_1I2R16Certificates_valid :
    CB1_6_1I2R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB1_6_1I2R16P_check : ∀ a : Fin 6, contains (CB1_6_1I2R16Raw a) (CB1_6_1I2R16P a) = true := by
  decide +kernel
lemma CB1_6_1I2R16P_sound (a : Fin 6) :
    (CB1_6_1I2R16P a).Encloses (CB1_6_1I2R16Value a) :=
  contains_sound (CB1_6_1I2R16Raw_sound a) (CB1_6_1I2R16P_check a)
lemma CB1_6_1I2R16Terms_sound (a : Fin 6) :
    (CB1_6_1I2R16Terms a).Encloses (Foundation.entropyTerm (CB1_6_1I2R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_6_1I2R16Certificates_valid
    (CB1_6_1I2R16CertificateIndex a) (CB1_6_1I2R16P_sound a)
lemma CB1_6_1I2R16Entropy_sound : CB1_6_1I2R16Entropy.Encloses (Foundation.finiteEntropy CB1_6_1I2R16Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_6_1I2R16Value CB1_6_1I2R16Terms CB1_6_1I2R16Terms_sound) (by decide +kernel)
lemma CB1_6_1I2R16Mass_sound : CB1_6_1I2R16Mass.Encloses (∑ a, CB1_6_1I2R16Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_6_1I2R16P CB1_6_1I2R16Value CB1_6_1I2R16P_sound) (by decide +kernel)
lemma CB1_6_1I2R16MassTerm_sound : CB1_6_1I2R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_6_1I2R16Value a))) :=
  entropyTerm_zero_ball (CB1_6_1I2R16Mass_sound)
lemma CB1_6_1I2R16H_sound : CB1_6_1I2R16H.Encloses (homogeneousEntropy CB1_6_1I2R16Value) := by
  exact contains_sound (homogeneous_enclosed CB1_6_1I2R16Value CB1_6_1I2R16MassTerm_sound CB1_6_1I2R16Entropy_sound) (by decide +kernel)
lemma CB1_6_1I2ResidualEntropies_sound_oai (k : Fin 17) :
    (CB1_6_1I2ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 1 6 1)) (fun u => (stageBLaw (shape 1 6 1) u : ℝ)) (stageBPriority (shape 1 6 1)) 2 (fun u a => (littleLaw (shape 1 6 1) u ((stageBPriority (shape 1 6 1)) 2) a : ℝ)) k)) := by
  fin_cases k
  · exact CB1_6_1I2R0H_sound
  · exact CB1_6_1I2R1H_sound
  · exact CB1_6_1I2R2H_sound
  · exact CB1_6_1I2R3H_sound
  · exact CB1_6_1I2R4H_sound
  · exact CB1_6_1I2R5H_sound
  · exact CB1_6_1I2R6H_sound
  · exact CB1_6_1I2R7H_sound
  · exact CB1_6_1I2R8H_sound
  · exact CB1_6_1I2R9H_sound
  · exact CB1_6_1I2R10H_sound
  · exact CB1_6_1I2R11H_sound
  · exact CB1_6_1I2R12H_sound
  · exact CB1_6_1I2R13H_sound
  · exact CB1_6_1I2R14H_sound
  · exact CB1_6_1I2R15H_sound
  · exact CB1_6_1I2R16H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB1_6_1I2ResidualEntropies_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB1_6_1I2ResidualEntropies_sound_oai
