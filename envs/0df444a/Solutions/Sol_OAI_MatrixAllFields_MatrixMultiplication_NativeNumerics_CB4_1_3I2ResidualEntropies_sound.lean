-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_1_3I2ResidualEntropies_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T14:42:32.477203+00:00
-- url     : https://prove2.me/submissions/15a571ad-2beb-4fdf-ae30-1995410d714e

import Mathlib
import Definitions.Def_OAIQ254M010
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkLog_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_finSumBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB4_1_3I2R0Entropy_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB4_1_3I2R0Mass_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB4_1_3I2R10H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB4_1_3I2R11MassTerm_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB4_1_3I2R11Terms_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB4_1_3I2R12H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB4_1_3I2R13H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB4_1_3I2R14H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB4_1_3I2R15H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB4_1_3I2R16H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB4_1_3I2R1H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB4_1_3I2R2H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB4_1_3I2R3H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB4_1_3I2R4Mass_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB4_1_3I2R4Terms_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB4_1_3I2R5H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB4_1_3I2R6H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB4_1_3I2R7Entropy_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB4_1_3I2R7Mass_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB4_1_3I2R8P_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB4_1_3I2R8Terms_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB4_1_3I2R9Raw_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB4_1_3I2R9Terms_sound
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
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB4_1_3I2
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
lemma CB4_1_3I2R0MassTermLog_sound : CB4_1_3I2R0MassTermLog.Encloses (Real.log ((∑ a, CB4_1_3I2R0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB4_1_3I2R0Mass_sound) (w := CB4_1_3I2R0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CB4_1_3I2R0MassTerm_sound : CB4_1_3I2R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_1_3I2R0Value a))) := by
  exact contains_sound (entropyTerm_ball (CB4_1_3I2R0Mass_sound) CB4_1_3I2R0MassTermLog_sound) (by decide +kernel)
lemma CB4_1_3I2R0H_sound : CB4_1_3I2R0H.Encloses (homogeneousEntropy CB4_1_3I2R0Value) := by
  exact contains_sound (homogeneous_enclosed CB4_1_3I2R0Value CB4_1_3I2R0MassTerm_sound CB4_1_3I2R0Entropy_sound) (by decide +kernel)
lemma CB4_1_3I2R4Entropy_sound : CB4_1_3I2R4Entropy.Encloses (Foundation.finiteEntropy CB4_1_3I2R4Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_1_3I2R4Value CB4_1_3I2R4Terms CB4_1_3I2R4Terms_sound) (by decide +kernel)
lemma CB4_1_3I2R4MassTerm_sound : CB4_1_3I2R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_1_3I2R4Value a))) :=
  entropyTerm_zero_ball (CB4_1_3I2R4Mass_sound)
lemma CB4_1_3I2R4H_sound : CB4_1_3I2R4H.Encloses (homogeneousEntropy CB4_1_3I2R4Value) := by
  exact contains_sound (homogeneous_enclosed CB4_1_3I2R4Value CB4_1_3I2R4MassTerm_sound CB4_1_3I2R4Entropy_sound) (by decide +kernel)
lemma CB4_1_3I2R7MassTerm_sound : CB4_1_3I2R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_1_3I2R7Value a))) :=
  entropyTerm_zero_ball (CB4_1_3I2R7Mass_sound)
lemma CB4_1_3I2R7H_sound : CB4_1_3I2R7H.Encloses (homogeneousEntropy CB4_1_3I2R7Value) := by
  exact contains_sound (homogeneous_enclosed CB4_1_3I2R7Value CB4_1_3I2R7MassTerm_sound CB4_1_3I2R7Entropy_sound) (by decide +kernel)
lemma CB4_1_3I2R8Entropy_sound : CB4_1_3I2R8Entropy.Encloses (Foundation.finiteEntropy CB4_1_3I2R8Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_1_3I2R8Value CB4_1_3I2R8Terms CB4_1_3I2R8Terms_sound) (by decide +kernel)
lemma CB4_1_3I2R8Mass_sound : CB4_1_3I2R8Mass.Encloses (∑ a, CB4_1_3I2R8Value a) := by
  exact contains_sound (finSumBall_sound 6 CB4_1_3I2R8P CB4_1_3I2R8Value CB4_1_3I2R8P_sound) (by decide +kernel)
lemma CB4_1_3I2R8MassTerm_sound : CB4_1_3I2R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_1_3I2R8Value a))) :=
  entropyTerm_zero_ball (CB4_1_3I2R8Mass_sound)
lemma CB4_1_3I2R8H_sound : CB4_1_3I2R8H.Encloses (homogeneousEntropy CB4_1_3I2R8Value) := by
  exact contains_sound (homogeneous_enclosed CB4_1_3I2R8Value CB4_1_3I2R8MassTerm_sound CB4_1_3I2R8Entropy_sound) (by decide +kernel)
lemma CB4_1_3I2R9P_check : ∀ a : Fin 6, contains (CB4_1_3I2R9Raw a) (CB4_1_3I2R9P a) = true := by
  decide +kernel
lemma CB4_1_3I2R9P_sound (a : Fin 6) :
    (CB4_1_3I2R9P a).Encloses (CB4_1_3I2R9Value a) :=
  contains_sound (CB4_1_3I2R9Raw_sound a) (CB4_1_3I2R9P_check a)
lemma CB4_1_3I2R9Entropy_sound : CB4_1_3I2R9Entropy.Encloses (Foundation.finiteEntropy CB4_1_3I2R9Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_1_3I2R9Value CB4_1_3I2R9Terms CB4_1_3I2R9Terms_sound) (by decide +kernel)
lemma CB4_1_3I2R9Mass_sound : CB4_1_3I2R9Mass.Encloses (∑ a, CB4_1_3I2R9Value a) := by
  exact contains_sound (finSumBall_sound 6 CB4_1_3I2R9P CB4_1_3I2R9Value CB4_1_3I2R9P_sound) (by decide +kernel)
lemma CB4_1_3I2R9MassTerm_sound : CB4_1_3I2R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_1_3I2R9Value a))) :=
  entropyTerm_zero_ball (CB4_1_3I2R9Mass_sound)
lemma CB4_1_3I2R9H_sound : CB4_1_3I2R9H.Encloses (homogeneousEntropy CB4_1_3I2R9Value) := by
  exact contains_sound (homogeneous_enclosed CB4_1_3I2R9Value CB4_1_3I2R9MassTerm_sound CB4_1_3I2R9Entropy_sound) (by decide +kernel)
lemma CB4_1_3I2R11Entropy_sound : CB4_1_3I2R11Entropy.Encloses (Foundation.finiteEntropy CB4_1_3I2R11Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_1_3I2R11Value CB4_1_3I2R11Terms CB4_1_3I2R11Terms_sound) (by decide +kernel)
lemma CB4_1_3I2R11H_sound : CB4_1_3I2R11H.Encloses (homogeneousEntropy CB4_1_3I2R11Value) := by
  exact contains_sound (homogeneous_enclosed CB4_1_3I2R11Value CB4_1_3I2R11MassTerm_sound CB4_1_3I2R11Entropy_sound) (by decide +kernel)
lemma CB4_1_3I2ResidualEntropies_sound_oai (k : Fin 17) :
    (CB4_1_3I2ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 4 1 3)) (fun u => (stageBLaw (shape 4 1 3) u : ℝ)) (stageBPriority (shape 4 1 3)) 2 (fun u a => (littleLaw (shape 4 1 3) u ((stageBPriority (shape 4 1 3)) 2) a : ℝ)) k)) := by
  fin_cases k
  · exact CB4_1_3I2R0H_sound
  · exact CB4_1_3I2R1H_sound
  · exact CB4_1_3I2R2H_sound
  · exact CB4_1_3I2R3H_sound
  · exact CB4_1_3I2R4H_sound
  · exact CB4_1_3I2R5H_sound
  · exact CB4_1_3I2R6H_sound
  · exact CB4_1_3I2R7H_sound
  · exact CB4_1_3I2R8H_sound
  · exact CB4_1_3I2R9H_sound
  · exact CB4_1_3I2R10H_sound
  · exact CB4_1_3I2R11H_sound
  · exact CB4_1_3I2R12H_sound
  · exact CB4_1_3I2R13H_sound
  · exact CB4_1_3I2R14H_sound
  · exact CB4_1_3I2R15H_sound
  · exact CB4_1_3I2R16H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_1_3I2ResidualEntropies_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_1_3I2ResidualEntropies_sound_oai
