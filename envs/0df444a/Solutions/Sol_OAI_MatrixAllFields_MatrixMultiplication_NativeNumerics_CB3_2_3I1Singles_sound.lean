-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I1Singles_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T09:07:25.022197+00:00
-- url     : https://prove2.me/submissions/72738372-db3f-489e-850a-b75ffca69754

import Mathlib
import Definitions.Def_OAIQ254M002
import Definitions.Def_OAIQ254M003
import Definitions.Def_OAIQ254M004
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkLog_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_finSumBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_2_3I1S2_2_0MassTerm_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_2_3I1S3_1_0Terms_sound
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

lemma log_exact_one_ball {p : ℝ} (hp : (Ball.exact 1).Encloses p) :
    (Ball.exact 0).Encloses (Real.log p) := by
  have hb := Ball.bounds hp
  have h : p = 1 := by norm_num [Ball.lower, Ball.upper, Ball.exact] at hb <;> linarith
  rw [h, Real.log_one]
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

lemma exact_rat_enclosed {q r : ℚ} (h : q = r) : (Ball.exact q).Encloses (r : ℝ) := by
  rw [h]
  exact Ball.exact_sound r

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
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitB5_1_2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators

lemma B3_2_3_below : below (shape 3 2 3) = [
  (shape 0 1 3),
  (shape 0 2 2),
  (shape 1 0 3),
  (shape 1 1 2),
  (shape 1 2 1),
  (shape 2 0 2),
  (shape 2 1 1),
  (shape 2 2 0),
  (shape 3 0 1),
  (shape 3 1 0)] := by decide +kernel

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_LittleB1_3_4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
lemma shapes4_list : shapes 4 = [
  (shape 0 0 4),
  (shape 0 1 3),
  (shape 0 2 2),
  (shape 0 3 1),
  (shape 0 4 0),
  (shape 1 0 3),
  (shape 1 1 2),
  (shape 1 2 1),
  (shape 1 3 0),
  (shape 2 0 2),
  (shape 2 1 1),
  (shape 2 2 0),
  (shape 3 0 1),
  (shape 3 1 0),
  (shape 4 0 0)] := by decide +kernel

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SupportedContraction
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
lemma B3_2_3Binary_eq (u : Shape) (hu : u ∈ shapes 4) :
    binaryParameter (shape 3 2 3) u = B3_2_3Binary u := by
  rw [shapes4_list] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

lemma B3_2_3Little_sound (u : Shape) (w : Fin 3) (i : Fin 6) :
    (B3_2_3Little u w i).Encloses (littleLaw (shape 3 2 3) u w i : ℝ) := by
  by_cases hu : u ∈ shapes 4
  · simp only [B3_2_3Little, hu, ite_true, if_true]
    apply exact_rat_enclosed
    simp only [B3_2_3LittleRat, littleLaw, B3_2_3Binary_eq u hu]
  · simp only [B3_2_3Little, hu, ite_false, if_false]
    exact Ball.exact_sound _

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB3_2_3I1
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
lemma CB3_2_3I1S2_2_0E_2Log_sound : CB3_2_3I1S2_2_0E_2Log.Encloses (Real.log (CB3_2_3I1S2_2_0Value (2 : Fin 6))) := by
  exact checkLog_sound logTwoBall_sound ((B3_2_3Little_sound (shape 2 2 0) ((stageBPriority (shape 3 2 3)) 1)) (2 : Fin 6)) (w := CB3_2_3I1S2_2_0E_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CB3_2_3I1S2_2_0E_2_sound : CB3_2_3I1S2_2_0E_2.Encloses (Foundation.entropyTerm (CB3_2_3I1S2_2_0Value (2 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B3_2_3Little_sound (shape 2 2 0) ((stageBPriority (shape 3 2 3)) 1)) (2 : Fin 6)) CB3_2_3I1S2_2_0E_2Log_sound) (by decide +kernel)
lemma CB3_2_3I1S2_2_0E_3Log_sound : CB3_2_3I1S2_2_0E_3Log.Encloses (Real.log (CB3_2_3I1S2_2_0Value (3 : Fin 6))) := by
  exact checkLog_sound logTwoBall_sound ((B3_2_3Little_sound (shape 2 2 0) ((stageBPriority (shape 3 2 3)) 1)) (3 : Fin 6)) (w := CB3_2_3I1S2_2_0E_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CB3_2_3I1S2_2_0E_3_sound : CB3_2_3I1S2_2_0E_3.Encloses (Foundation.entropyTerm (CB3_2_3I1S2_2_0Value (3 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B3_2_3Little_sound (shape 2 2 0) ((stageBPriority (shape 3 2 3)) 1)) (3 : Fin 6)) CB3_2_3I1S2_2_0E_3Log_sound) (by decide +kernel)
lemma CB3_2_3I1S2_2_0Terms_sound (a : Fin 6) :
    (CB3_2_3I1S2_2_0Terms a).Encloses (Foundation.entropyTerm (CB3_2_3I1S2_2_0Value a)) := by
  fin_cases a
  · exact (entropyTerm_zero_ball ((B3_2_3Little_sound (shape 2 2 0) ((stageBPriority (shape 3 2 3)) 1)) (0 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B3_2_3Little_sound (shape 2 2 0) ((stageBPriority (shape 3 2 3)) 1)) (1 : Fin 6)))
  · exact CB3_2_3I1S2_2_0E_2_sound
  · exact CB3_2_3I1S2_2_0E_3_sound
  · exact (entropyTerm_zero_ball ((B3_2_3Little_sound (shape 2 2 0) ((stageBPriority (shape 3 2 3)) 1)) (4 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B3_2_3Little_sound (shape 2 2 0) ((stageBPriority (shape 3 2 3)) 1)) (5 : Fin 6)))
lemma CB3_2_3I1S2_2_0Entropy_sound : CB3_2_3I1S2_2_0Entropy.Encloses (Foundation.finiteEntropy CB3_2_3I1S2_2_0Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_2_3I1S2_2_0Value CB3_2_3I1S2_2_0Terms CB3_2_3I1S2_2_0Terms_sound) (by decide +kernel)
lemma CB3_2_3I1S2_2_0H_sound : CB3_2_3I1S2_2_0H.Encloses (homogeneousEntropy CB3_2_3I1S2_2_0Value) := by
  exact contains_sound (homogeneous_enclosed CB3_2_3I1S2_2_0Value CB3_2_3I1S2_2_0MassTerm_sound CB3_2_3I1S2_2_0Entropy_sound) (by decide +kernel)
lemma CB3_2_3I1S3_1_0Entropy_sound : CB3_2_3I1S3_1_0Entropy.Encloses (Foundation.finiteEntropy CB3_2_3I1S3_1_0Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_2_3I1S3_1_0Value CB3_2_3I1S3_1_0Terms CB3_2_3I1S3_1_0Terms_sound) (by decide +kernel)
lemma CB3_2_3I1S3_1_0Mass_sound : CB3_2_3I1S3_1_0Mass.Encloses (∑ a, CB3_2_3I1S3_1_0Value a) := by
  exact contains_sound (finSumBall_sound 6 (B3_2_3Little (shape 3 1 0) ((stageBPriority (shape 3 2 3)) 1)) CB3_2_3I1S3_1_0Value (B3_2_3Little_sound (shape 3 1 0) ((stageBPriority (shape 3 2 3)) 1))) (by decide +kernel)
lemma CB3_2_3I1S3_1_0MassTermLog_sound : CB3_2_3I1S3_1_0MassTermLog.Encloses (Real.log ((∑ a, CB3_2_3I1S3_1_0Value a))) := by
  exact log_exact_one_ball (CB3_2_3I1S3_1_0Mass_sound)
lemma CB3_2_3I1S3_1_0MassTerm_sound : CB3_2_3I1S3_1_0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_2_3I1S3_1_0Value a))) := by
  exact contains_sound (entropyTerm_ball (CB3_2_3I1S3_1_0Mass_sound) CB3_2_3I1S3_1_0MassTermLog_sound) (by decide +kernel)
lemma CB3_2_3I1S3_1_0H_sound : CB3_2_3I1S3_1_0H.Encloses (homogeneousEntropy CB3_2_3I1S3_1_0Value) := by
  exact contains_sound (homogeneous_enclosed CB3_2_3I1S3_1_0Value CB3_2_3I1S3_1_0MassTerm_sound CB3_2_3I1S3_1_0Entropy_sound) (by decide +kernel)
lemma CB3_2_3I1Singles_sound_oai (u : Shape) (hu : u ∈ below (shape 3 2 3))
    (hd : designated (stageBPriority (shape 3 2 3)) 1 u) :
    (CB3_2_3I1Singles u).Encloses (homogeneousEntropy ((fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) u)) := by
  rw [B3_2_3_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (show ¬ designated (stageBPriority (shape 3 2 3)) 1 (shape 0 1 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (stageBPriority (shape 3 2 3)) 1 (shape 0 2 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (stageBPriority (shape 3 2 3)) 1 (shape 1 0 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (stageBPriority (shape 3 2 3)) 1 (shape 1 1 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (stageBPriority (shape 3 2 3)) 1 (shape 1 2 1) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (stageBPriority (shape 3 2 3)) 1 (shape 2 0 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (stageBPriority (shape 3 2 3)) 1 (shape 2 1 1) by decide +kernel) hd |>.elim
  · exact CB3_2_3I1S2_2_0H_sound
  · exact (show ¬ designated (stageBPriority (shape 3 2 3)) 1 (shape 3 0 1) by decide +kernel) hd |>.elim
  · exact CB3_2_3I1S3_1_0H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I1Singles_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I1Singles_sound_oai
