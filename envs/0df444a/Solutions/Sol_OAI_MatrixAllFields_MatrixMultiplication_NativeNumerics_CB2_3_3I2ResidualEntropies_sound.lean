-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB2_3_3I2ResidualEntropies_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T13:26:04.628691+00:00
-- url     : https://prove2.me/submissions/f8343deb-b7b0-4fc9-8489-5db9041b22b2

import Mathlib
import Definitions.Def_OAIQ254M010
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_finSumBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_CompactCertificate_entropyLookup_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_3_3I2R0H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_3_3I2R10Entropy_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_3_3I2R10Mass_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_3_3I2R11Entropy_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_3_3I2R11P_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_3_3I2R12Entropy_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_3_3I2R12Raw_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_3_3I2R13Raw_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_3_3I2R13Terms_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_3_3I2R14Raw_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_3_3I2R14Terms_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_3_3I2R15Raw_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_3_3I2R15Terms_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_3_3I2R16H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_3_3I2R1H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_3_3I2R2H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_3_3I2R3H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_3_3I2R4H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_3_3I2R5Entropy_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_3_3I2R5Raw_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_3_3I2R6Raw_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_3_3I2R6Terms_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_3_3I2R7H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_3_3I2R8H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_3_3I2R9Raw_sound
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
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB2_3_3I2
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
lemma CB2_3_3I2R5P_check : ∀ a : Fin 6, contains (CB2_3_3I2R5Raw a) (CB2_3_3I2R5P a) = true := by
  decide +kernel
lemma CB2_3_3I2R5P_sound (a : Fin 6) :
    (CB2_3_3I2R5P a).Encloses (CB2_3_3I2R5Value a) :=
  contains_sound (CB2_3_3I2R5Raw_sound a) (CB2_3_3I2R5P_check a)
lemma CB2_3_3I2R5Mass_sound : CB2_3_3I2R5Mass.Encloses (∑ a, CB2_3_3I2R5Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_3_3I2R5P CB2_3_3I2R5Value CB2_3_3I2R5P_sound) (by decide +kernel)
lemma CB2_3_3I2R5MassTerm_sound : CB2_3_3I2R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_3_3I2R5Value a))) :=
  entropyTerm_zero_ball (CB2_3_3I2R5Mass_sound)
lemma CB2_3_3I2R5H_sound : CB2_3_3I2R5H.Encloses (homogeneousEntropy CB2_3_3I2R5Value) := by
  exact contains_sound (homogeneous_enclosed CB2_3_3I2R5Value CB2_3_3I2R5MassTerm_sound CB2_3_3I2R5Entropy_sound) (by decide +kernel)
lemma CB2_3_3I2R6P_check : ∀ a : Fin 6, contains (CB2_3_3I2R6Raw a) (CB2_3_3I2R6P a) = true := by
  decide +kernel
lemma CB2_3_3I2R6P_sound (a : Fin 6) :
    (CB2_3_3I2R6P a).Encloses (CB2_3_3I2R6Value a) :=
  contains_sound (CB2_3_3I2R6Raw_sound a) (CB2_3_3I2R6P_check a)
lemma CB2_3_3I2R6Entropy_sound : CB2_3_3I2R6Entropy.Encloses (Foundation.finiteEntropy CB2_3_3I2R6Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_3_3I2R6Value CB2_3_3I2R6Terms CB2_3_3I2R6Terms_sound) (by decide +kernel)
lemma CB2_3_3I2R6Mass_sound : CB2_3_3I2R6Mass.Encloses (∑ a, CB2_3_3I2R6Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_3_3I2R6P CB2_3_3I2R6Value CB2_3_3I2R6P_sound) (by decide +kernel)
lemma CB2_3_3I2R6MassTerm_sound : CB2_3_3I2R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_3_3I2R6Value a))) :=
  entropyTerm_zero_ball (CB2_3_3I2R6Mass_sound)
lemma CB2_3_3I2R6H_sound : CB2_3_3I2R6H.Encloses (homogeneousEntropy CB2_3_3I2R6Value) := by
  exact contains_sound (homogeneous_enclosed CB2_3_3I2R6Value CB2_3_3I2R6MassTerm_sound CB2_3_3I2R6Entropy_sound) (by decide +kernel)
lemma CB2_3_3I2R9Certificates_valid :
    CB2_3_3I2R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB2_3_3I2R9P_check : ∀ a : Fin 6, contains (CB2_3_3I2R9Raw a) (CB2_3_3I2R9P a) = true := by
  decide +kernel
lemma CB2_3_3I2R9P_sound (a : Fin 6) :
    (CB2_3_3I2R9P a).Encloses (CB2_3_3I2R9Value a) :=
  contains_sound (CB2_3_3I2R9Raw_sound a) (CB2_3_3I2R9P_check a)
lemma CB2_3_3I2R9Terms_sound (a : Fin 6) :
    (CB2_3_3I2R9Terms a).Encloses (Foundation.entropyTerm (CB2_3_3I2R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_3_3I2R9Certificates_valid
    (CB2_3_3I2R9CertificateIndex a) (CB2_3_3I2R9P_sound a)
lemma CB2_3_3I2R9Entropy_sound : CB2_3_3I2R9Entropy.Encloses (Foundation.finiteEntropy CB2_3_3I2R9Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_3_3I2R9Value CB2_3_3I2R9Terms CB2_3_3I2R9Terms_sound) (by decide +kernel)
lemma CB2_3_3I2R9Mass_sound : CB2_3_3I2R9Mass.Encloses (∑ a, CB2_3_3I2R9Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_3_3I2R9P CB2_3_3I2R9Value CB2_3_3I2R9P_sound) (by decide +kernel)
lemma CB2_3_3I2R9MassTerm_sound : CB2_3_3I2R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_3_3I2R9Value a))) :=
  entropyTerm_zero_ball (CB2_3_3I2R9Mass_sound)
lemma CB2_3_3I2R9H_sound : CB2_3_3I2R9H.Encloses (homogeneousEntropy CB2_3_3I2R9Value) := by
  exact contains_sound (homogeneous_enclosed CB2_3_3I2R9Value CB2_3_3I2R9MassTerm_sound CB2_3_3I2R9Entropy_sound) (by decide +kernel)
lemma CB2_3_3I2R10MassTerm_sound : CB2_3_3I2R10MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_3_3I2R10Value a))) :=
  entropyTerm_zero_ball (CB2_3_3I2R10Mass_sound)
lemma CB2_3_3I2R10H_sound : CB2_3_3I2R10H.Encloses (homogeneousEntropy CB2_3_3I2R10Value) := by
  exact contains_sound (homogeneous_enclosed CB2_3_3I2R10Value CB2_3_3I2R10MassTerm_sound CB2_3_3I2R10Entropy_sound) (by decide +kernel)
lemma CB2_3_3I2R11Mass_sound : CB2_3_3I2R11Mass.Encloses (∑ a, CB2_3_3I2R11Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_3_3I2R11P CB2_3_3I2R11Value CB2_3_3I2R11P_sound) (by decide +kernel)
lemma CB2_3_3I2R11MassTerm_sound : CB2_3_3I2R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_3_3I2R11Value a))) :=
  entropyTerm_zero_ball (CB2_3_3I2R11Mass_sound)
lemma CB2_3_3I2R11H_sound : CB2_3_3I2R11H.Encloses (homogeneousEntropy CB2_3_3I2R11Value) := by
  exact contains_sound (homogeneous_enclosed CB2_3_3I2R11Value CB2_3_3I2R11MassTerm_sound CB2_3_3I2R11Entropy_sound) (by decide +kernel)
lemma CB2_3_3I2R12P_check : ∀ a : Fin 6, contains (CB2_3_3I2R12Raw a) (CB2_3_3I2R12P a) = true := by
  decide +kernel
lemma CB2_3_3I2R12P_sound (a : Fin 6) :
    (CB2_3_3I2R12P a).Encloses (CB2_3_3I2R12Value a) :=
  contains_sound (CB2_3_3I2R12Raw_sound a) (CB2_3_3I2R12P_check a)
lemma CB2_3_3I2R12Mass_sound : CB2_3_3I2R12Mass.Encloses (∑ a, CB2_3_3I2R12Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_3_3I2R12P CB2_3_3I2R12Value CB2_3_3I2R12P_sound) (by decide +kernel)
lemma CB2_3_3I2R12MassTerm_sound : CB2_3_3I2R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_3_3I2R12Value a))) :=
  entropyTerm_zero_ball (CB2_3_3I2R12Mass_sound)
lemma CB2_3_3I2R12H_sound : CB2_3_3I2R12H.Encloses (homogeneousEntropy CB2_3_3I2R12Value) := by
  exact contains_sound (homogeneous_enclosed CB2_3_3I2R12Value CB2_3_3I2R12MassTerm_sound CB2_3_3I2R12Entropy_sound) (by decide +kernel)
lemma CB2_3_3I2R13P_check : ∀ a : Fin 6, contains (CB2_3_3I2R13Raw a) (CB2_3_3I2R13P a) = true := by
  decide +kernel
lemma CB2_3_3I2R13P_sound (a : Fin 6) :
    (CB2_3_3I2R13P a).Encloses (CB2_3_3I2R13Value a) :=
  contains_sound (CB2_3_3I2R13Raw_sound a) (CB2_3_3I2R13P_check a)
lemma CB2_3_3I2R13Entropy_sound : CB2_3_3I2R13Entropy.Encloses (Foundation.finiteEntropy CB2_3_3I2R13Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_3_3I2R13Value CB2_3_3I2R13Terms CB2_3_3I2R13Terms_sound) (by decide +kernel)
lemma CB2_3_3I2R13Mass_sound : CB2_3_3I2R13Mass.Encloses (∑ a, CB2_3_3I2R13Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_3_3I2R13P CB2_3_3I2R13Value CB2_3_3I2R13P_sound) (by decide +kernel)
lemma CB2_3_3I2R13MassTerm_sound : CB2_3_3I2R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_3_3I2R13Value a))) :=
  entropyTerm_zero_ball (CB2_3_3I2R13Mass_sound)
lemma CB2_3_3I2R13H_sound : CB2_3_3I2R13H.Encloses (homogeneousEntropy CB2_3_3I2R13Value) := by
  exact contains_sound (homogeneous_enclosed CB2_3_3I2R13Value CB2_3_3I2R13MassTerm_sound CB2_3_3I2R13Entropy_sound) (by decide +kernel)
lemma CB2_3_3I2R14P_check : ∀ a : Fin 6, contains (CB2_3_3I2R14Raw a) (CB2_3_3I2R14P a) = true := by
  decide +kernel
lemma CB2_3_3I2R14P_sound (a : Fin 6) :
    (CB2_3_3I2R14P a).Encloses (CB2_3_3I2R14Value a) :=
  contains_sound (CB2_3_3I2R14Raw_sound a) (CB2_3_3I2R14P_check a)
lemma CB2_3_3I2R14Entropy_sound : CB2_3_3I2R14Entropy.Encloses (Foundation.finiteEntropy CB2_3_3I2R14Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_3_3I2R14Value CB2_3_3I2R14Terms CB2_3_3I2R14Terms_sound) (by decide +kernel)
lemma CB2_3_3I2R14Mass_sound : CB2_3_3I2R14Mass.Encloses (∑ a, CB2_3_3I2R14Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_3_3I2R14P CB2_3_3I2R14Value CB2_3_3I2R14P_sound) (by decide +kernel)
lemma CB2_3_3I2R14MassTerm_sound : CB2_3_3I2R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_3_3I2R14Value a))) :=
  entropyTerm_zero_ball (CB2_3_3I2R14Mass_sound)
lemma CB2_3_3I2R14H_sound : CB2_3_3I2R14H.Encloses (homogeneousEntropy CB2_3_3I2R14Value) := by
  exact contains_sound (homogeneous_enclosed CB2_3_3I2R14Value CB2_3_3I2R14MassTerm_sound CB2_3_3I2R14Entropy_sound) (by decide +kernel)
lemma CB2_3_3I2R15P_check : ∀ a : Fin 6, contains (CB2_3_3I2R15Raw a) (CB2_3_3I2R15P a) = true := by
  decide +kernel
lemma CB2_3_3I2R15P_sound (a : Fin 6) :
    (CB2_3_3I2R15P a).Encloses (CB2_3_3I2R15Value a) :=
  contains_sound (CB2_3_3I2R15Raw_sound a) (CB2_3_3I2R15P_check a)
lemma CB2_3_3I2R15Entropy_sound : CB2_3_3I2R15Entropy.Encloses (Foundation.finiteEntropy CB2_3_3I2R15Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_3_3I2R15Value CB2_3_3I2R15Terms CB2_3_3I2R15Terms_sound) (by decide +kernel)
lemma CB2_3_3I2R15Mass_sound : CB2_3_3I2R15Mass.Encloses (∑ a, CB2_3_3I2R15Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_3_3I2R15P CB2_3_3I2R15Value CB2_3_3I2R15P_sound) (by decide +kernel)
lemma CB2_3_3I2R15MassTerm_sound : CB2_3_3I2R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_3_3I2R15Value a))) :=
  entropyTerm_zero_ball (CB2_3_3I2R15Mass_sound)
lemma CB2_3_3I2R15H_sound : CB2_3_3I2R15H.Encloses (homogeneousEntropy CB2_3_3I2R15Value) := by
  exact contains_sound (homogeneous_enclosed CB2_3_3I2R15Value CB2_3_3I2R15MassTerm_sound CB2_3_3I2R15Entropy_sound) (by decide +kernel)
lemma CB2_3_3I2ResidualEntropies_sound_oai (k : Fin 17) :
    (CB2_3_3I2ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 2 (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 2) a : ℝ)) k)) := by
  fin_cases k
  · exact CB2_3_3I2R0H_sound
  · exact CB2_3_3I2R1H_sound
  · exact CB2_3_3I2R2H_sound
  · exact CB2_3_3I2R3H_sound
  · exact CB2_3_3I2R4H_sound
  · exact CB2_3_3I2R5H_sound
  · exact CB2_3_3I2R6H_sound
  · exact CB2_3_3I2R7H_sound
  · exact CB2_3_3I2R8H_sound
  · exact CB2_3_3I2R9H_sound
  · exact CB2_3_3I2R10H_sound
  · exact CB2_3_3I2R11H_sound
  · exact CB2_3_3I2R12H_sound
  · exact CB2_3_3I2R13H_sound
  · exact CB2_3_3I2R14H_sound
  · exact CB2_3_3I2R15H_sound
  · exact CB2_3_3I2R16H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB2_3_3I2ResidualEntropies_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB2_3_3I2ResidualEntropies_sound_oai
