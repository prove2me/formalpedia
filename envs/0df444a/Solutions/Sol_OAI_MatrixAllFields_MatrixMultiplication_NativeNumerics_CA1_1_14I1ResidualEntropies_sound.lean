-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_1_14I1ResidualEntropies_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:29:58.982117+00:00
-- url     : https://prove2.me/submissions/f5539398-a297-42a7-b55c-5436e7ab3bee

import Mathlib
import Definitions.Def_OAIQ254M007
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_1_14I1R0H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_1_14I1R10H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_1_14I1R11H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_1_14I1R12H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_1_14I1R13H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_1_14I1R14Entropy_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_1_14I1R14Mass_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_1_14I1R15H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_1_14I1R16H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_1_14I1R1H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_1_14I1R2H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_1_14I1R3H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_1_14I1R4H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_1_14I1R5H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_1_14I1R6H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_1_14I1R7Entropy_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_1_14I1R7Mass_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_1_14I1R8Entropy_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_1_14I1R8Mass_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_1_14I1R9Entropy_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_1_14I1R9Mass_sound
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

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_1_14I1
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
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
lemma CA1_1_14I1R7MassTerm_sound : CA1_1_14I1R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_1_14I1R7Value a))) :=
  entropyTerm_zero_ball (CA1_1_14I1R7Mass_sound)
lemma CA1_1_14I1R7H_sound : CA1_1_14I1R7H.Encloses (homogeneousEntropy CA1_1_14I1R7Value) := by
  exact contains_sound (homogeneous_enclosed CA1_1_14I1R7Value CA1_1_14I1R7MassTerm_sound CA1_1_14I1R7Entropy_sound) (by decide +kernel)
lemma CA1_1_14I1R8MassTerm_sound : CA1_1_14I1R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_1_14I1R8Value a))) :=
  entropyTerm_zero_ball (CA1_1_14I1R8Mass_sound)
lemma CA1_1_14I1R8H_sound : CA1_1_14I1R8H.Encloses (homogeneousEntropy CA1_1_14I1R8Value) := by
  exact contains_sound (homogeneous_enclosed CA1_1_14I1R8Value CA1_1_14I1R8MassTerm_sound CA1_1_14I1R8Entropy_sound) (by decide +kernel)
lemma CA1_1_14I1R9MassTerm_sound : CA1_1_14I1R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_1_14I1R9Value a))) :=
  entropyTerm_zero_ball (CA1_1_14I1R9Mass_sound)
lemma CA1_1_14I1R9H_sound : CA1_1_14I1R9H.Encloses (homogeneousEntropy CA1_1_14I1R9Value) := by
  exact contains_sound (homogeneous_enclosed CA1_1_14I1R9Value CA1_1_14I1R9MassTerm_sound CA1_1_14I1R9Entropy_sound) (by decide +kernel)
lemma CA1_1_14I1R14MassTerm_sound : CA1_1_14I1R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_1_14I1R14Value a))) :=
  entropyTerm_zero_ball (CA1_1_14I1R14Mass_sound)
lemma CA1_1_14I1R14H_sound : CA1_1_14I1R14H.Encloses (homogeneousEntropy CA1_1_14I1R14Value) := by
  exact contains_sound (homogeneous_enclosed CA1_1_14I1R14Value CA1_1_14I1R14MassTerm_sound CA1_1_14I1R14Entropy_sound) (by decide +kernel)
lemma CA1_1_14I1ResidualEntropies_sound_oai (k : Fin 17) :
    (CA1_1_14I1ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 1 1 14)) (fun u => (stageALaw (shape 1 1 14) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) k)) := by
  fin_cases k
  · exact CA1_1_14I1R0H_sound
  · exact CA1_1_14I1R1H_sound
  · exact CA1_1_14I1R2H_sound
  · exact CA1_1_14I1R3H_sound
  · exact CA1_1_14I1R4H_sound
  · exact CA1_1_14I1R5H_sound
  · exact CA1_1_14I1R6H_sound
  · exact CA1_1_14I1R7H_sound
  · exact CA1_1_14I1R8H_sound
  · exact CA1_1_14I1R9H_sound
  · exact CA1_1_14I1R10H_sound
  · exact CA1_1_14I1R11H_sound
  · exact CA1_1_14I1R12H_sound
  · exact CA1_1_14I1R13H_sound
  · exact CA1_1_14I1R14H_sound
  · exact CA1_1_14I1R15H_sound
  · exact CA1_1_14I1R16H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_1_14I1ResidualEntropies_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_1_14I1ResidualEntropies_sound_oai
