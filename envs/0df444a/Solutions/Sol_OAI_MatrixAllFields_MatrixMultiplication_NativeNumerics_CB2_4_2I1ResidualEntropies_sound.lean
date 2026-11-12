-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB2_4_2I1ResidualEntropies_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T13:28:21.11541+00:00
-- url     : https://prove2.me/submissions/3835782e-8372-47ec-8460-f0134d81cb53

import Mathlib
import Definitions.Def_OAIQ254M010
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkLog_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_finSumBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_CompactCertificate_entropyLookup_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_4_2I1R0MassTermLog_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_4_2I1R0Mass_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_4_2I1R0Raw_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_4_2I1R10H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_4_2I1R11MassTerm_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_4_2I1R11Raw_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_4_2I1R12H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_4_2I1R13H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_4_2I1R14H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_4_2I1R15H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_4_2I1R16H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_4_2I1R1MassTerm_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_4_2I1R1Raw_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_4_2I1R2Raw_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_4_2I1R2Terms_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_4_2I1R3H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_4_2I1R4Mass_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_4_2I1R4Terms_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_4_2I1R5H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_4_2I1R6H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_4_2I1R7H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_4_2I1R8H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_4_2I1R9H_sound
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
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB2_4_2I1
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
lemma CB2_4_2I1R0Certificates_valid :
    CB2_4_2I1R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB2_4_2I1R0P_check : ∀ a : Fin 6, contains (CB2_4_2I1R0Raw a) (CB2_4_2I1R0P a) = true := by
  decide +kernel
lemma CB2_4_2I1R0P_sound (a : Fin 6) :
    (CB2_4_2I1R0P a).Encloses (CB2_4_2I1R0Value a) :=
  contains_sound (CB2_4_2I1R0Raw_sound a) (CB2_4_2I1R0P_check a)
lemma CB2_4_2I1R0Terms_sound (a : Fin 6) :
    (CB2_4_2I1R0Terms a).Encloses (Foundation.entropyTerm (CB2_4_2I1R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_4_2I1R0Certificates_valid
    (CB2_4_2I1R0CertificateIndex a) (CB2_4_2I1R0P_sound a)
lemma CB2_4_2I1R0Entropy_sound : CB2_4_2I1R0Entropy.Encloses (Foundation.finiteEntropy CB2_4_2I1R0Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_4_2I1R0Value CB2_4_2I1R0Terms CB2_4_2I1R0Terms_sound) (by decide +kernel)
lemma CB2_4_2I1R0MassTerm_sound : CB2_4_2I1R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_4_2I1R0Value a))) := by
  exact contains_sound (entropyTerm_ball (CB2_4_2I1R0Mass_sound) CB2_4_2I1R0MassTermLog_sound) (by decide +kernel)
lemma CB2_4_2I1R0H_sound : CB2_4_2I1R0H.Encloses (homogeneousEntropy CB2_4_2I1R0Value) := by
  exact contains_sound (homogeneous_enclosed CB2_4_2I1R0Value CB2_4_2I1R0MassTerm_sound CB2_4_2I1R0Entropy_sound) (by decide +kernel)
lemma CB2_4_2I1R1Certificates_valid :
    CB2_4_2I1R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB2_4_2I1R1P_check : ∀ a : Fin 6, contains (CB2_4_2I1R1Raw a) (CB2_4_2I1R1P a) = true := by
  decide +kernel
lemma CB2_4_2I1R1P_sound (a : Fin 6) :
    (CB2_4_2I1R1P a).Encloses (CB2_4_2I1R1Value a) :=
  contains_sound (CB2_4_2I1R1Raw_sound a) (CB2_4_2I1R1P_check a)
lemma CB2_4_2I1R1Terms_sound (a : Fin 6) :
    (CB2_4_2I1R1Terms a).Encloses (Foundation.entropyTerm (CB2_4_2I1R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_4_2I1R1Certificates_valid
    (CB2_4_2I1R1CertificateIndex a) (CB2_4_2I1R1P_sound a)
lemma CB2_4_2I1R1Entropy_sound : CB2_4_2I1R1Entropy.Encloses (Foundation.finiteEntropy CB2_4_2I1R1Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_4_2I1R1Value CB2_4_2I1R1Terms CB2_4_2I1R1Terms_sound) (by decide +kernel)
lemma CB2_4_2I1R1H_sound : CB2_4_2I1R1H.Encloses (homogeneousEntropy CB2_4_2I1R1Value) := by
  exact contains_sound (homogeneous_enclosed CB2_4_2I1R1Value CB2_4_2I1R1MassTerm_sound CB2_4_2I1R1Entropy_sound) (by decide +kernel)
lemma CB2_4_2I1R2P_check : ∀ a : Fin 6, contains (CB2_4_2I1R2Raw a) (CB2_4_2I1R2P a) = true := by
  decide +kernel
lemma CB2_4_2I1R2P_sound (a : Fin 6) :
    (CB2_4_2I1R2P a).Encloses (CB2_4_2I1R2Value a) :=
  contains_sound (CB2_4_2I1R2Raw_sound a) (CB2_4_2I1R2P_check a)
lemma CB2_4_2I1R2Entropy_sound : CB2_4_2I1R2Entropy.Encloses (Foundation.finiteEntropy CB2_4_2I1R2Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_4_2I1R2Value CB2_4_2I1R2Terms CB2_4_2I1R2Terms_sound) (by decide +kernel)
lemma CB2_4_2I1R2Mass_sound : CB2_4_2I1R2Mass.Encloses (∑ a, CB2_4_2I1R2Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_4_2I1R2P CB2_4_2I1R2Value CB2_4_2I1R2P_sound) (by decide +kernel)
lemma CB2_4_2I1R2MassTermLog_sound : CB2_4_2I1R2MassTermLog.Encloses (Real.log ((∑ a, CB2_4_2I1R2Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB2_4_2I1R2Mass_sound) (w := CB2_4_2I1R2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CB2_4_2I1R2MassTerm_sound : CB2_4_2I1R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_4_2I1R2Value a))) := by
  exact contains_sound (entropyTerm_ball (CB2_4_2I1R2Mass_sound) CB2_4_2I1R2MassTermLog_sound) (by decide +kernel)
lemma CB2_4_2I1R2H_sound : CB2_4_2I1R2H.Encloses (homogeneousEntropy CB2_4_2I1R2Value) := by
  exact contains_sound (homogeneous_enclosed CB2_4_2I1R2Value CB2_4_2I1R2MassTerm_sound CB2_4_2I1R2Entropy_sound) (by decide +kernel)
lemma CB2_4_2I1R4Entropy_sound : CB2_4_2I1R4Entropy.Encloses (Foundation.finiteEntropy CB2_4_2I1R4Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_4_2I1R4Value CB2_4_2I1R4Terms CB2_4_2I1R4Terms_sound) (by decide +kernel)
lemma CB2_4_2I1R4MassTerm_sound : CB2_4_2I1R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_4_2I1R4Value a))) :=
  entropyTerm_zero_ball (CB2_4_2I1R4Mass_sound)
lemma CB2_4_2I1R4H_sound : CB2_4_2I1R4H.Encloses (homogeneousEntropy CB2_4_2I1R4Value) := by
  exact contains_sound (homogeneous_enclosed CB2_4_2I1R4Value CB2_4_2I1R4MassTerm_sound CB2_4_2I1R4Entropy_sound) (by decide +kernel)
lemma CB2_4_2I1R11Certificates_valid :
    CB2_4_2I1R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB2_4_2I1R11P_check : ∀ a : Fin 6, contains (CB2_4_2I1R11Raw a) (CB2_4_2I1R11P a) = true := by
  decide +kernel
lemma CB2_4_2I1R11P_sound (a : Fin 6) :
    (CB2_4_2I1R11P a).Encloses (CB2_4_2I1R11Value a) :=
  contains_sound (CB2_4_2I1R11Raw_sound a) (CB2_4_2I1R11P_check a)
lemma CB2_4_2I1R11Terms_sound (a : Fin 6) :
    (CB2_4_2I1R11Terms a).Encloses (Foundation.entropyTerm (CB2_4_2I1R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_4_2I1R11Certificates_valid
    (CB2_4_2I1R11CertificateIndex a) (CB2_4_2I1R11P_sound a)
lemma CB2_4_2I1R11Entropy_sound : CB2_4_2I1R11Entropy.Encloses (Foundation.finiteEntropy CB2_4_2I1R11Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_4_2I1R11Value CB2_4_2I1R11Terms CB2_4_2I1R11Terms_sound) (by decide +kernel)
lemma CB2_4_2I1R11H_sound : CB2_4_2I1R11H.Encloses (homogeneousEntropy CB2_4_2I1R11Value) := by
  exact contains_sound (homogeneous_enclosed CB2_4_2I1R11Value CB2_4_2I1R11MassTerm_sound CB2_4_2I1R11Entropy_sound) (by decide +kernel)
lemma CB2_4_2I1ResidualEntropies_sound_oai (k : Fin 17) :
    (CB2_4_2I1ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 2 4 2)) (fun u => (stageBLaw (shape 2 4 2) u : ℝ)) (stageBPriority (shape 2 4 2)) 1 (fun u a => (littleLaw (shape 2 4 2) u ((stageBPriority (shape 2 4 2)) 1) a : ℝ)) k)) := by
  fin_cases k
  · exact CB2_4_2I1R0H_sound
  · exact CB2_4_2I1R1H_sound
  · exact CB2_4_2I1R2H_sound
  · exact CB2_4_2I1R3H_sound
  · exact CB2_4_2I1R4H_sound
  · exact CB2_4_2I1R5H_sound
  · exact CB2_4_2I1R6H_sound
  · exact CB2_4_2I1R7H_sound
  · exact CB2_4_2I1R8H_sound
  · exact CB2_4_2I1R9H_sound
  · exact CB2_4_2I1R10H_sound
  · exact CB2_4_2I1R11H_sound
  · exact CB2_4_2I1R12H_sound
  · exact CB2_4_2I1R13H_sound
  · exact CB2_4_2I1R14H_sound
  · exact CB2_4_2I1R15H_sound
  · exact CB2_4_2I1R16H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB2_4_2I1ResidualEntropies_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB2_4_2I1ResidualEntropies_sound_oai
