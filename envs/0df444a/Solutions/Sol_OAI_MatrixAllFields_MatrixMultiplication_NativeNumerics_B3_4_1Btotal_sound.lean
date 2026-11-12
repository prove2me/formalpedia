-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_4_1Btotal_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:57:49.155199+00:00
-- url     : https://prove2.me/submissions/5d9ccfd3-aefe-4f27-84c7-2ca1ee9a5973

import Mathlib
import Definitions.Def_OAIQ254M002
import Definitions.Def_OAIQ254M003
import Definitions.Def_OAIQ254M005
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_mul_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkLog_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B3_4_1Masses_sound
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
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal3_4_1
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
lemma B3_4_1U1_2_1D_sound : B3_4_1U1_2_1D.Encloses (binaryParameter (shape 3 4 1) (shape 1 2 1) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
lemma B3_4_1U1_2_1OneD_sound : B3_4_1U1_2_1OneD.Encloses (1 - (binaryParameter (shape 3 4 1) (shape 1 2 1) : ℝ)) := by
  have he : binaryParameter (shape 3 4 1) (shape 1 2 1) = (2953 / 1000000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((997047 / 1000000) : ℚ) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [B3_4_1U1_2_1OneD, Ball.exact])
lemma B3_4_1U1_2_1EDLog_sound : B3_4_1U1_2_1EDLog.Encloses (Real.log ((binaryParameter (shape 3 4 1) (shape 1 2 1) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B3_4_1U1_2_1D_sound) (w := B3_4_1U1_2_1EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma B3_4_1U1_2_1ED_sound : B3_4_1U1_2_1ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 3 4 1) (shape 1 2 1) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B3_4_1U1_2_1D_sound) B3_4_1U1_2_1EDLog_sound) (by decide +kernel)
lemma B3_4_1U1_2_1EOneDLog_sound : B3_4_1U1_2_1EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 3 4 1) (shape 1 2 1) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B3_4_1U1_2_1OneD_sound) (w := B3_4_1U1_2_1EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma B3_4_1U1_2_1EOneD_sound : B3_4_1U1_2_1EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 3 4 1) (shape 1 2 1) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B3_4_1U1_2_1OneD_sound) B3_4_1U1_2_1EOneDLog_sound) (by decide +kernel)
lemma B3_4_1U1_2_1BinaryEntropy_sound : B3_4_1U1_2_1BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 3 4 1) (shape 1 2 1))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B3_4_1U1_2_1EOneD_sound B3_4_1U1_2_1ED_sound)
    (Ball.mul_sound B3_4_1U1_2_1D_sound logN2_sound)) (by decide +kernel)
lemma B3_4_1U2_1_1D_sound : B3_4_1U2_1_1D.Encloses (binaryParameter (shape 3 4 1) (shape 2 1 1) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
lemma B3_4_1U2_1_1OneD_sound : B3_4_1U2_1_1OneD.Encloses (1 - (binaryParameter (shape 3 4 1) (shape 2 1 1) : ℝ)) := by
  have he : binaryParameter (shape 3 4 1) (shape 2 1 1) = (21083 / 500000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((478917 / 500000) : ℚ) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [B3_4_1U2_1_1OneD, Ball.exact])
lemma B3_4_1U2_1_1EDLog_sound : B3_4_1U2_1_1EDLog.Encloses (Real.log ((binaryParameter (shape 3 4 1) (shape 2 1 1) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B3_4_1U2_1_1D_sound) (w := B3_4_1U2_1_1EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma B3_4_1U2_1_1ED_sound : B3_4_1U2_1_1ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 3 4 1) (shape 2 1 1) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B3_4_1U2_1_1D_sound) B3_4_1U2_1_1EDLog_sound) (by decide +kernel)
lemma B3_4_1U2_1_1EOneDLog_sound : B3_4_1U2_1_1EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 3 4 1) (shape 2 1 1) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B3_4_1U2_1_1OneD_sound) (w := B3_4_1U2_1_1EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma B3_4_1U2_1_1EOneD_sound : B3_4_1U2_1_1EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 3 4 1) (shape 2 1 1) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B3_4_1U2_1_1OneD_sound) B3_4_1U2_1_1EOneDLog_sound) (by decide +kernel)
lemma B3_4_1U2_1_1BinaryEntropy_sound : B3_4_1U2_1_1BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 3 4 1) (shape 2 1 1))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B3_4_1U2_1_1EOneD_sound B3_4_1U2_1_1ED_sound)
    (Ball.mul_sound B3_4_1U2_1_1D_sound logN2_sound)) (by decide +kernel)
lemma B3_4_1Binaries_sound (u : Shape) (hu : u ∈ (below (shape 3 4 1)).filter positive) :
    (B3_4_1Binaries u).Encloses ((fun u => binaryEntropyRate (binaryParameter (shape 3 4 1) u)) u) := by
  have hl : (below (shape 3 4 1)).filter positive = [(shape 1 2 1), (shape 2 1 1)] := by decide +kernel
  rw [hl] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl
  · exact B3_4_1U1_2_1BinaryEntropy_sound
  · exact B3_4_1U2_1_1BinaryEntropy_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_NativeInterior
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
lemma B3_4_1Btotal_sound_oai : B3_4_1Btotal.Encloses
    ((((below (shape 3 4 1)).filter positive).map (fun u => (littleMass (shape 3 4 1) u : ℝ) * (2 * Real.log 2 + binaryEntropyRate (binaryParameter (shape 3 4 1) u)))).sum) := by
  exact contains_sound (listSumBall_sound ((below (shape 3 4 1)).filter positive)
    (fun u => .mul (B3_4_1Masses u) (.add (.mul (.exact 2) logN2) (B3_4_1Binaries u))) _
    (fun u hu => Ball.mul_sound (B3_4_1Masses_sound u (List.mem_filter.mp hu).1)
      (Ball.add_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
        logN2_sound) (B3_4_1Binaries_sound u hu)))) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_4_1Btotal_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_4_1Btotal_sound_oai
