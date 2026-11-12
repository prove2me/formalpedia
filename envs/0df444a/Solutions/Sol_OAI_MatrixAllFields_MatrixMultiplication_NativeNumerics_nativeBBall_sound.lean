-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.nativeBBall_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:58:39.063616+00:00
-- url     : https://prove2.me/submissions/25515a7b-faa8-4b28-ad52-b04f2b218d2b

import Mathlib
import Definitions.Def_OAIQ254M005
import Definitions.Def_OAIQ254M007
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_mul_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkLog_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B1_1_6Btotal_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B1_2_5Masses_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B1_3_4Btotal_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B1_4_3Btotal_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B1_5_2Btotal_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B1_6_1Masses_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B2_1_5Masses_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B2_2_4Btotal_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B2_3_3Btotal_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B2_4_2Btotal_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B2_5_1Btotal_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B3_1_4Btotal_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B3_2_3Masses_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B3_3_2Btotal_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B3_4_1Btotal_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B4_1_3Btotal_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B4_2_2Btotal_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B4_3_1Btotal_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B5_1_2Btotal_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B5_2_1Btotal_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B6_1_1Btotal_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_entropyTerm_ball

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

theorem add_sound {a b : Ball} {x y : ℝ} (hx : a.Encloses x) (hy : b.Encloses y) :
    (add a b).Encloses (x + y) := by
  unfold Encloses add
  simp only [Rat.cast_add]
  calc
    _ = |(x - (a.center : ℝ)) + (y - (b.center : ℝ))| := by congr 1; ring
    _ ≤ |x - (a.center : ℝ)| + |y - (b.center : ℝ)| := abs_add_le _ _
    _ ≤ _ := add_le_add hx hy

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

namespace MatrixMultiplication.AllFieldInitialEntropyCertificate
open AllFieldParameters AllFieldCertificates AllFieldCertificates.Replay
open scoped BigOperators

lemma listSumBall_sound {α : Type*} (xs : List α) (b : α → Ball) (v : α → ℝ)
    (h : ∀ x ∈ xs, (b x).Encloses (v x)) :
    (listSumBall xs b).Encloses ((xs.map v).sum) := by
  induction xs with
  | nil => simpa [listSumBall] using Ball.exact_sound 0
  | cons x xs ih =>
    simpa only [listSumBall, List.foldr_cons, List.map_cons, List.sum_cons] using
      Ball.add_sound (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

end MatrixMultiplication.AllFieldInitialEntropyCertificate

end
end

end MatrixAllFields

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
lemma logN2_sound : logN2.Encloses (Real.log ((2 : ℝ))) := by
  exact checkLog_sound logTwoBall_sound ((by convert Ball.exact_sound (2 : ℚ) using 1; norm_num)) (w := logN2Witness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_InitialProbabilities
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
lemma positiveSecond_list : positiveSecond = [
  (shape 1 1 6),
  (shape 1 2 5),
  (shape 1 3 4),
  (shape 1 4 3),
  (shape 1 5 2),
  (shape 1 6 1),
  (shape 2 1 5),
  (shape 2 2 4),
  (shape 2 3 3),
  (shape 2 4 2),
  (shape 2 5 1),
  (shape 3 1 4),
  (shape 3 2 3),
  (shape 3 3 2),
  (shape 3 4 1),
  (shape 4 1 3),
  (shape 4 2 2),
  (shape 4 3 1),
  (shape 5 1 2),
  (shape 5 2 1),
  (shape 6 1 1)] := by decide +kernel

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal1_2_5
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inr
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
lemma B1_2_5U1_1_2D_sound : B1_2_5U1_1_2D.Encloses (binaryParameter (shape 1 2 5) (shape 1 1 2) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
lemma B1_2_5U1_1_2OneD_sound : B1_2_5U1_1_2OneD.Encloses (1 - (binaryParameter (shape 1 2 5) (shape 1 1 2) : ℝ)) := by
  have he : binaryParameter (shape 1 2 5) (shape 1 1 2) = 0 := by decide +kernel
  rw [he]
  convert Ball.exact_sound (1 : ℚ) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [B1_2_5U1_1_2OneD, Ball.exact])
lemma B1_2_5U1_1_2ED_sound : B1_2_5U1_1_2ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 1 2 5) (shape 1 1 2) : ℝ))) :=
  entropyTerm_zero_ball (B1_2_5U1_1_2D_sound)
lemma B1_2_5U1_1_2EOneDLog_sound : B1_2_5U1_1_2EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 1 2 5) (shape 1 1 2) : ℝ)))) := by
  exact log_exact_one_ball (B1_2_5U1_1_2OneD_sound)
lemma B1_2_5U1_1_2EOneD_sound : B1_2_5U1_1_2EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 1 2 5) (shape 1 1 2) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B1_2_5U1_1_2OneD_sound) B1_2_5U1_1_2EOneDLog_sound) (by decide +kernel)
lemma B1_2_5U1_1_2BinaryEntropy_sound : B1_2_5U1_1_2BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 1 2 5) (shape 1 1 2))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B1_2_5U1_1_2EOneD_sound B1_2_5U1_1_2ED_sound)
    (Ball.mul_sound B1_2_5U1_1_2D_sound logN2_sound)) (by decide +kernel)
lemma B1_2_5U1_2_1D_sound : B1_2_5U1_2_1D.Encloses (binaryParameter (shape 1 2 5) (shape 1 2 1) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
lemma B1_2_5U1_2_1OneD_sound : B1_2_5U1_2_1OneD.Encloses (1 - (binaryParameter (shape 1 2 5) (shape 1 2 1) : ℝ)) := by
  have he : binaryParameter (shape 1 2 5) (shape 1 2 1) = (10533 / 250000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((239467 / 250000) : ℚ) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [B1_2_5U1_2_1OneD, Ball.exact])
lemma B1_2_5U1_2_1EDLog_sound : B1_2_5U1_2_1EDLog.Encloses (Real.log ((binaryParameter (shape 1 2 5) (shape 1 2 1) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B1_2_5U1_2_1D_sound) (w := B1_2_5U1_2_1EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma B1_2_5U1_2_1ED_sound : B1_2_5U1_2_1ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 1 2 5) (shape 1 2 1) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B1_2_5U1_2_1D_sound) B1_2_5U1_2_1EDLog_sound) (by decide +kernel)
lemma B1_2_5U1_2_1EOneDLog_sound : B1_2_5U1_2_1EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 1 2 5) (shape 1 2 1) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B1_2_5U1_2_1OneD_sound) (w := B1_2_5U1_2_1EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma B1_2_5U1_2_1EOneD_sound : B1_2_5U1_2_1EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 1 2 5) (shape 1 2 1) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B1_2_5U1_2_1OneD_sound) B1_2_5U1_2_1EOneDLog_sound) (by decide +kernel)
lemma B1_2_5U1_2_1BinaryEntropy_sound : B1_2_5U1_2_1BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 1 2 5) (shape 1 2 1))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B1_2_5U1_2_1EOneD_sound B1_2_5U1_2_1ED_sound)
    (Ball.mul_sound B1_2_5U1_2_1D_sound logN2_sound)) (by decide +kernel)
lemma B1_2_5Binaries_sound (u : Shape) (hu : u ∈ (below (shape 1 2 5)).filter positive) :
    (B1_2_5Binaries u).Encloses ((fun u => binaryEntropyRate (binaryParameter (shape 1 2 5) u)) u) := by
  have hl : (below (shape 1 2 5)).filter positive = [(shape 1 1 2), (shape 1 2 1)] := by decide +kernel
  rw [hl] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl
  · exact B1_2_5U1_1_2BinaryEntropy_sound
  · exact B1_2_5U1_2_1BinaryEntropy_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal1_6_1
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inr
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
lemma B1_6_1U1_2_1D_sound : B1_6_1U1_2_1D.Encloses (binaryParameter (shape 1 6 1) (shape 1 2 1) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
lemma B1_6_1U1_2_1OneD_sound : B1_6_1U1_2_1OneD.Encloses (1 - (binaryParameter (shape 1 6 1) (shape 1 2 1) : ℝ)) := by
  have he : binaryParameter (shape 1 6 1) (shape 1 2 1) = (41991 / 1000000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((958009 / 1000000) : ℚ) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [B1_6_1U1_2_1OneD, Ball.exact])
lemma B1_6_1U1_2_1EDLog_sound : B1_6_1U1_2_1EDLog.Encloses (Real.log ((binaryParameter (shape 1 6 1) (shape 1 2 1) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B1_6_1U1_2_1D_sound) (w := B1_6_1U1_2_1EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma B1_6_1U1_2_1ED_sound : B1_6_1U1_2_1ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 1 6 1) (shape 1 2 1) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B1_6_1U1_2_1D_sound) B1_6_1U1_2_1EDLog_sound) (by decide +kernel)
lemma B1_6_1U1_2_1EOneDLog_sound : B1_6_1U1_2_1EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 1 6 1) (shape 1 2 1) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B1_6_1U1_2_1OneD_sound) (w := B1_6_1U1_2_1EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma B1_6_1U1_2_1EOneD_sound : B1_6_1U1_2_1EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 1 6 1) (shape 1 2 1) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B1_6_1U1_2_1OneD_sound) B1_6_1U1_2_1EOneDLog_sound) (by decide +kernel)
lemma B1_6_1U1_2_1BinaryEntropy_sound : B1_6_1U1_2_1BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 1 6 1) (shape 1 2 1))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B1_6_1U1_2_1EOneD_sound B1_6_1U1_2_1ED_sound)
    (Ball.mul_sound B1_6_1U1_2_1D_sound logN2_sound)) (by decide +kernel)
lemma B1_6_1Binaries_sound (u : Shape) (hu : u ∈ (below (shape 1 6 1)).filter positive) :
    (B1_6_1Binaries u).Encloses ((fun u => binaryEntropyRate (binaryParameter (shape 1 6 1) u)) u) := by
  have hl : (below (shape 1 6 1)).filter positive = [(shape 1 2 1)] := by decide +kernel
  rw [hl] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl
  · exact B1_6_1U1_2_1BinaryEntropy_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal2_1_5
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inr
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
lemma B2_1_5U1_1_2D_sound : B2_1_5U1_1_2D.Encloses (binaryParameter (shape 2 1 5) (shape 1 1 2) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
lemma B2_1_5U1_1_2OneD_sound : B2_1_5U1_1_2OneD.Encloses (1 - (binaryParameter (shape 2 1 5) (shape 1 1 2) : ℝ)) := by
  have he : binaryParameter (shape 2 1 5) (shape 1 1 2) = (1 / 1000000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((999999 / 1000000) : ℚ) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [B2_1_5U1_1_2OneD, Ball.exact])
lemma B2_1_5U1_1_2EDLog_sound : B2_1_5U1_1_2EDLog.Encloses (Real.log ((binaryParameter (shape 2 1 5) (shape 1 1 2) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B2_1_5U1_1_2D_sound) (w := B2_1_5U1_1_2EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma B2_1_5U1_1_2ED_sound : B2_1_5U1_1_2ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 2 1 5) (shape 1 1 2) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B2_1_5U1_1_2D_sound) B2_1_5U1_1_2EDLog_sound) (by decide +kernel)
lemma B2_1_5U1_1_2EOneDLog_sound : B2_1_5U1_1_2EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 2 1 5) (shape 1 1 2) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B2_1_5U1_1_2OneD_sound) (w := B2_1_5U1_1_2EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma B2_1_5U1_1_2EOneD_sound : B2_1_5U1_1_2EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 2 1 5) (shape 1 1 2) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B2_1_5U1_1_2OneD_sound) B2_1_5U1_1_2EOneDLog_sound) (by decide +kernel)
lemma B2_1_5U1_1_2BinaryEntropy_sound : B2_1_5U1_1_2BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 2 1 5) (shape 1 1 2))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B2_1_5U1_1_2EOneD_sound B2_1_5U1_1_2ED_sound)
    (Ball.mul_sound B2_1_5U1_1_2D_sound logN2_sound)) (by decide +kernel)
lemma B2_1_5U2_1_1D_sound : B2_1_5U2_1_1D.Encloses (binaryParameter (shape 2 1 5) (shape 2 1 1) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
lemma B2_1_5U2_1_1OneD_sound : B2_1_5U2_1_1OneD.Encloses (1 - (binaryParameter (shape 2 1 5) (shape 2 1 1) : ℝ)) := by
  have he : binaryParameter (shape 2 1 5) (shape 2 1 1) = (21083 / 500000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((478917 / 500000) : ℚ) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [B2_1_5U2_1_1OneD, Ball.exact])
lemma B2_1_5U2_1_1EDLog_sound : B2_1_5U2_1_1EDLog.Encloses (Real.log ((binaryParameter (shape 2 1 5) (shape 2 1 1) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B2_1_5U2_1_1D_sound) (w := B2_1_5U2_1_1EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma B2_1_5U2_1_1ED_sound : B2_1_5U2_1_1ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 2 1 5) (shape 2 1 1) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B2_1_5U2_1_1D_sound) B2_1_5U2_1_1EDLog_sound) (by decide +kernel)
lemma B2_1_5U2_1_1EOneDLog_sound : B2_1_5U2_1_1EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 2 1 5) (shape 2 1 1) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B2_1_5U2_1_1OneD_sound) (w := B2_1_5U2_1_1EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma B2_1_5U2_1_1EOneD_sound : B2_1_5U2_1_1EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 2 1 5) (shape 2 1 1) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B2_1_5U2_1_1OneD_sound) B2_1_5U2_1_1EOneDLog_sound) (by decide +kernel)
lemma B2_1_5U2_1_1BinaryEntropy_sound : B2_1_5U2_1_1BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 2 1 5) (shape 2 1 1))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B2_1_5U2_1_1EOneD_sound B2_1_5U2_1_1ED_sound)
    (Ball.mul_sound B2_1_5U2_1_1D_sound logN2_sound)) (by decide +kernel)
lemma B2_1_5Binaries_sound (u : Shape) (hu : u ∈ (below (shape 2 1 5)).filter positive) :
    (B2_1_5Binaries u).Encloses ((fun u => binaryEntropyRate (binaryParameter (shape 2 1 5) u)) u) := by
  have hl : (below (shape 2 1 5)).filter positive = [(shape 1 1 2), (shape 2 1 1)] := by decide +kernel
  rw [hl] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl
  · exact B2_1_5U1_1_2BinaryEntropy_sound
  · exact B2_1_5U2_1_1BinaryEntropy_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal3_2_3
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inr
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
lemma B3_2_3U1_1_2D_sound : B3_2_3U1_1_2D.Encloses (binaryParameter (shape 3 2 3) (shape 1 1 2) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
lemma B3_2_3U1_1_2OneD_sound : B3_2_3U1_1_2OneD.Encloses (1 - (binaryParameter (shape 3 2 3) (shape 1 1 2) : ℝ)) := by
  have he : binaryParameter (shape 3 2 3) (shape 1 1 2) = (947 / 200000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((199053 / 200000) : ℚ) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [B3_2_3U1_1_2OneD, Ball.exact])
lemma B3_2_3U1_1_2EDLog_sound : B3_2_3U1_1_2EDLog.Encloses (Real.log ((binaryParameter (shape 3 2 3) (shape 1 1 2) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B3_2_3U1_1_2D_sound) (w := B3_2_3U1_1_2EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma B3_2_3U1_1_2ED_sound : B3_2_3U1_1_2ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 3 2 3) (shape 1 1 2) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B3_2_3U1_1_2D_sound) B3_2_3U1_1_2EDLog_sound) (by decide +kernel)
lemma B3_2_3U1_1_2EOneDLog_sound : B3_2_3U1_1_2EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 3 2 3) (shape 1 1 2) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B3_2_3U1_1_2OneD_sound) (w := B3_2_3U1_1_2EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma B3_2_3U1_1_2EOneD_sound : B3_2_3U1_1_2EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 3 2 3) (shape 1 1 2) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B3_2_3U1_1_2OneD_sound) B3_2_3U1_1_2EOneDLog_sound) (by decide +kernel)
lemma B3_2_3U1_1_2BinaryEntropy_sound : B3_2_3U1_1_2BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 3 2 3) (shape 1 1 2))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B3_2_3U1_1_2EOneD_sound B3_2_3U1_1_2ED_sound)
    (Ball.mul_sound B3_2_3U1_1_2D_sound logN2_sound)) (by decide +kernel)
lemma B3_2_3U1_2_1D_sound : B3_2_3U1_2_1D.Encloses (binaryParameter (shape 3 2 3) (shape 1 2 1) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
lemma B3_2_3U1_2_1OneD_sound : B3_2_3U1_2_1OneD.Encloses (1 - (binaryParameter (shape 3 2 3) (shape 1 2 1) : ℝ)) := by
  have he : binaryParameter (shape 3 2 3) (shape 1 2 1) = (38889 / 1000000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((961111 / 1000000) : ℚ) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [B3_2_3U1_2_1OneD, Ball.exact])
lemma B3_2_3U1_2_1EDLog_sound : B3_2_3U1_2_1EDLog.Encloses (Real.log ((binaryParameter (shape 3 2 3) (shape 1 2 1) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B3_2_3U1_2_1D_sound) (w := B3_2_3U1_2_1EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma B3_2_3U1_2_1ED_sound : B3_2_3U1_2_1ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 3 2 3) (shape 1 2 1) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B3_2_3U1_2_1D_sound) B3_2_3U1_2_1EDLog_sound) (by decide +kernel)
lemma B3_2_3U1_2_1EOneDLog_sound : B3_2_3U1_2_1EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 3 2 3) (shape 1 2 1) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B3_2_3U1_2_1OneD_sound) (w := B3_2_3U1_2_1EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma B3_2_3U1_2_1EOneD_sound : B3_2_3U1_2_1EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 3 2 3) (shape 1 2 1) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B3_2_3U1_2_1OneD_sound) B3_2_3U1_2_1EOneDLog_sound) (by decide +kernel)
lemma B3_2_3U1_2_1BinaryEntropy_sound : B3_2_3U1_2_1BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 3 2 3) (shape 1 2 1))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B3_2_3U1_2_1EOneD_sound B3_2_3U1_2_1ED_sound)
    (Ball.mul_sound B3_2_3U1_2_1D_sound logN2_sound)) (by decide +kernel)
lemma B3_2_3U2_1_1D_sound : B3_2_3U2_1_1D.Encloses (binaryParameter (shape 3 2 3) (shape 2 1 1) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
lemma B3_2_3U2_1_1OneD_sound : B3_2_3U2_1_1OneD.Encloses (1 - (binaryParameter (shape 3 2 3) (shape 2 1 1) : ℝ)) := by
  have he : binaryParameter (shape 3 2 3) (shape 2 1 1) = (21083 / 500000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((478917 / 500000) : ℚ) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [B3_2_3U2_1_1OneD, Ball.exact])
lemma B3_2_3U2_1_1EDLog_sound : B3_2_3U2_1_1EDLog.Encloses (Real.log ((binaryParameter (shape 3 2 3) (shape 2 1 1) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B3_2_3U2_1_1D_sound) (w := B3_2_3U2_1_1EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma B3_2_3U2_1_1ED_sound : B3_2_3U2_1_1ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 3 2 3) (shape 2 1 1) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B3_2_3U2_1_1D_sound) B3_2_3U2_1_1EDLog_sound) (by decide +kernel)
lemma B3_2_3U2_1_1EOneDLog_sound : B3_2_3U2_1_1EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 3 2 3) (shape 2 1 1) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B3_2_3U2_1_1OneD_sound) (w := B3_2_3U2_1_1EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma B3_2_3U2_1_1EOneD_sound : B3_2_3U2_1_1EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 3 2 3) (shape 2 1 1) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B3_2_3U2_1_1OneD_sound) B3_2_3U2_1_1EOneDLog_sound) (by decide +kernel)
lemma B3_2_3U2_1_1BinaryEntropy_sound : B3_2_3U2_1_1BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 3 2 3) (shape 2 1 1))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B3_2_3U2_1_1EOneD_sound B3_2_3U2_1_1ED_sound)
    (Ball.mul_sound B3_2_3U2_1_1D_sound logN2_sound)) (by decide +kernel)
lemma B3_2_3Binaries_sound (u : Shape) (hu : u ∈ (below (shape 3 2 3)).filter positive) :
    (B3_2_3Binaries u).Encloses ((fun u => binaryEntropyRate (binaryParameter (shape 3 2 3) u)) u) := by
  have hl : (below (shape 3 2 3)).filter positive = [(shape 1 1 2), (shape 1 2 1), (shape 2 1 1)] := by decide +kernel
  rw [hl] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl
  · exact B3_2_3U1_1_2BinaryEntropy_sound
  · exact B3_2_3U1_2_1BinaryEntropy_sound
  · exact B3_2_3U2_1_1BinaryEntropy_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_NativeInterior
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.shapeValue_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.bWeight_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inr _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inr
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
lemma interior_fold (f : Shape × Shape → ℝ) :
    (interiorPairs.map f).sum = (positiveSecond.map (fun t =>
      (((below t).filter positive).map (fun u => f (t,u))).sum)).sum := by
  have h (xs : List Shape) :
      ((xs.flatMap (fun t => ((below t).filter positive).map (fun u => (t,u)))).map f).sum =
      (xs.map (fun t => (((below t).filter positive).map (fun u => f (t,u))).sum)).sum := by
    induction xs with
    | nil => simp
    | cons t xs ih => simp only [List.flatMap_cons, List.map_append, List.sum_append,
        List.map_map, Function.comp_def, List.map_cons, List.sum_cons, ih]
  exact h positiveSecond
lemma B1_2_5Btotal_sound : B1_2_5Btotal.Encloses
    ((((below (shape 1 2 5)).filter positive).map (fun u => (littleMass (shape 1 2 5) u : ℝ) * (2 * Real.log 2 + binaryEntropyRate (binaryParameter (shape 1 2 5) u)))).sum) := by
  exact contains_sound (listSumBall_sound ((below (shape 1 2 5)).filter positive)
    (fun u => .mul (B1_2_5Masses u) (.add (.mul (.exact 2) logN2) (B1_2_5Binaries u))) _
    (fun u hu => Ball.mul_sound (B1_2_5Masses_sound u (List.mem_filter.mp hu).1)
      (Ball.add_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
        logN2_sound) (B1_2_5Binaries_sound u hu)))) (by decide +kernel)
lemma B1_6_1Btotal_sound : B1_6_1Btotal.Encloses
    ((((below (shape 1 6 1)).filter positive).map (fun u => (littleMass (shape 1 6 1) u : ℝ) * (2 * Real.log 2 + binaryEntropyRate (binaryParameter (shape 1 6 1) u)))).sum) := by
  exact contains_sound (listSumBall_sound ((below (shape 1 6 1)).filter positive)
    (fun u => .mul (B1_6_1Masses u) (.add (.mul (.exact 2) logN2) (B1_6_1Binaries u))) _
    (fun u hu => Ball.mul_sound (B1_6_1Masses_sound u (List.mem_filter.mp hu).1)
      (Ball.add_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
        logN2_sound) (B1_6_1Binaries_sound u hu)))) (by decide +kernel)
lemma B2_1_5Btotal_sound : B2_1_5Btotal.Encloses
    ((((below (shape 2 1 5)).filter positive).map (fun u => (littleMass (shape 2 1 5) u : ℝ) * (2 * Real.log 2 + binaryEntropyRate (binaryParameter (shape 2 1 5) u)))).sum) := by
  exact contains_sound (listSumBall_sound ((below (shape 2 1 5)).filter positive)
    (fun u => .mul (B2_1_5Masses u) (.add (.mul (.exact 2) logN2) (B2_1_5Binaries u))) _
    (fun u hu => Ball.mul_sound (B2_1_5Masses_sound u (List.mem_filter.mp hu).1)
      (Ball.add_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
        logN2_sound) (B2_1_5Binaries_sound u hu)))) (by decide +kernel)
lemma B3_2_3Btotal_sound : B3_2_3Btotal.Encloses
    ((((below (shape 3 2 3)).filter positive).map (fun u => (littleMass (shape 3 2 3) u : ℝ) * (2 * Real.log 2 + binaryEntropyRate (binaryParameter (shape 3 2 3) u)))).sum) := by
  exact contains_sound (listSumBall_sound ((below (shape 3 2 3)).filter positive)
    (fun u => .mul (B3_2_3Masses u) (.add (.mul (.exact 2) logN2) (B3_2_3Binaries u))) _
    (fun u hu => Ball.mul_sound (B3_2_3Masses_sound u (List.mem_filter.mp hu).1)
      (Ball.add_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
        logN2_sound) (B3_2_3Binaries_sound u hu)))) (by decide +kernel)
lemma BParentBalls_sound (t : Shape) (ht : t ∈ positiveSecond) :
    (BParentBalls t).Encloses ((((below t).filter positive).map
      (fun u => (fun tu => interiorMass tu * (2 * Real.log 2 + interiorEntropy tu)) (t,u))).sum) := by
  rw [positiveSecond_list] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B1_1_6Btotal_sound
  · exact B1_2_5Btotal_sound
  · exact B1_3_4Btotal_sound
  · exact B1_4_3Btotal_sound
  · exact B1_5_2Btotal_sound
  · exact B1_6_1Btotal_sound
  · exact B2_1_5Btotal_sound
  · exact B2_2_4Btotal_sound
  · exact B2_3_3Btotal_sound
  · exact B2_4_2Btotal_sound
  · exact B2_5_1Btotal_sound
  · exact B3_1_4Btotal_sound
  · exact B3_2_3Btotal_sound
  · exact B3_3_2Btotal_sound
  · exact B3_4_1Btotal_sound
  · exact B4_1_3Btotal_sound
  · exact B4_2_2Btotal_sound
  · exact B4_3_1Btotal_sound
  · exact B5_1_2Btotal_sound
  · exact B5_2_1Btotal_sound
  · exact B6_1_1Btotal_sound
lemma nativeBBall_sound_oai : nativeBBall.Encloses nativeB := by
  rw [nativeB, interior_fold]
  have hb := contains_sound (Ball.mul_sound
    (listSumBall_sound positiveSecond BParentBalls _ BParentBalls_sound)
    (show (Ball.exact (1/3)).Encloses (1/(3 : ℝ)) by
      convert Ball.exact_sound (1/3) using 1
      all_goals try with_reducible_and_instances rfl
      norm_num))
    (show contains (.mul (listSumBall positiveSecond BParentBalls) (.exact (1/3))) nativeBBall = true by decide +kernel)
  simpa only [one_div, div_eq_mul_inv, one_mul] using hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.nativeBBall_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.nativeBBall_sound_oai
