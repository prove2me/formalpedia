-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_5_2Btotal_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T07:21:22.845611+00:00
-- url     : https://prove2.me/submissions/d8b77d63-2dd2-442b-935e-7843b9456548

import Mathlib
import Definitions.Def_OAIQ254M002
import Definitions.Def_OAIQ254M003
import Definitions.Def_OAIQ254M005
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_mul_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkLog_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B1_5_2Masses_sound
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

theorem widen_sound {a b : Ball} {x : ℝ} (hx : a.Encloses x)
    (h : |a.center - b.center| + a.radius ≤ b.radius) : b.Encloses x := by
  have hc : |(a.center : ℝ) - (b.center : ℝ)| + (a.radius : ℝ) ≤ (b.radius : ℝ) := by
    exact_mod_cast h
  unfold Encloses
  calc
    _ = |(x - (a.center : ℝ)) + ((a.center : ℝ) - (b.center : ℝ))| := by congr 1; ring
    _ ≤ |x - (a.center : ℝ)| + |(a.center : ℝ) - (b.center : ℝ)| := abs_add_le _ _
    _ ≤ (a.radius : ℝ) + |(a.center : ℝ) - (b.center : ℝ)| := add_le_add hx (le_refl _)
    _ ≤ _ := by linarith

end Ball

end MatrixMultiplication.AllFieldCertificates

end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.AllFieldCertificates.Replay

open MatrixMultiplication.Foundation.RationalLogCertificate

theorem contains_sound {a b : Ball} {x : ℝ}
    (ha : a.Encloses x) (hab : contains a b = true) : b.Encloses x :=
  Ball.widen_sound ha (of_decide_eq_true hab)

end MatrixMultiplication.AllFieldCertificates.Replay

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
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal1_5_2
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
lemma B1_5_2U1_1_2D_sound : B1_5_2U1_1_2D.Encloses (binaryParameter (shape 1 5 2) (shape 1 1 2) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
lemma B1_5_2U1_1_2OneD_sound : B1_5_2U1_1_2OneD.Encloses (1 - (binaryParameter (shape 1 5 2) (shape 1 1 2) : ℝ)) := by
  have he : binaryParameter (shape 1 5 2) (shape 1 1 2) = (10523 / 250000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((239477 / 250000) : ℚ) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [B1_5_2U1_1_2OneD, Ball.exact])
lemma B1_5_2U1_1_2EDLog_sound : B1_5_2U1_1_2EDLog.Encloses (Real.log ((binaryParameter (shape 1 5 2) (shape 1 1 2) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B1_5_2U1_1_2D_sound) (w := B1_5_2U1_1_2EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma B1_5_2U1_1_2ED_sound : B1_5_2U1_1_2ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 1 5 2) (shape 1 1 2) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B1_5_2U1_1_2D_sound) B1_5_2U1_1_2EDLog_sound) (by decide +kernel)
lemma B1_5_2U1_1_2EOneDLog_sound : B1_5_2U1_1_2EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 1 5 2) (shape 1 1 2) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B1_5_2U1_1_2OneD_sound) (w := B1_5_2U1_1_2EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma B1_5_2U1_1_2EOneD_sound : B1_5_2U1_1_2EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 1 5 2) (shape 1 1 2) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B1_5_2U1_1_2OneD_sound) B1_5_2U1_1_2EOneDLog_sound) (by decide +kernel)
lemma B1_5_2U1_1_2BinaryEntropy_sound : B1_5_2U1_1_2BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 1 5 2) (shape 1 1 2))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B1_5_2U1_1_2EOneD_sound B1_5_2U1_1_2ED_sound)
    (Ball.mul_sound B1_5_2U1_1_2D_sound logN2_sound)) (by decide +kernel)
lemma B1_5_2U1_2_1D_sound : B1_5_2U1_2_1D.Encloses (binaryParameter (shape 1 5 2) (shape 1 2 1) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
lemma B1_5_2U1_2_1OneD_sound : B1_5_2U1_2_1OneD.Encloses (1 - (binaryParameter (shape 1 5 2) (shape 1 2 1) : ℝ)) := by
  have he : binaryParameter (shape 1 5 2) (shape 1 2 1) = (3747 / 1000000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((996253 / 1000000) : ℚ) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [B1_5_2U1_2_1OneD, Ball.exact])
lemma B1_5_2U1_2_1EDLog_sound : B1_5_2U1_2_1EDLog.Encloses (Real.log ((binaryParameter (shape 1 5 2) (shape 1 2 1) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B1_5_2U1_2_1D_sound) (w := B1_5_2U1_2_1EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma B1_5_2U1_2_1ED_sound : B1_5_2U1_2_1ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 1 5 2) (shape 1 2 1) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B1_5_2U1_2_1D_sound) B1_5_2U1_2_1EDLog_sound) (by decide +kernel)
lemma B1_5_2U1_2_1EOneDLog_sound : B1_5_2U1_2_1EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 1 5 2) (shape 1 2 1) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B1_5_2U1_2_1OneD_sound) (w := B1_5_2U1_2_1EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma B1_5_2U1_2_1EOneD_sound : B1_5_2U1_2_1EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 1 5 2) (shape 1 2 1) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B1_5_2U1_2_1OneD_sound) B1_5_2U1_2_1EOneDLog_sound) (by decide +kernel)
lemma B1_5_2U1_2_1BinaryEntropy_sound : B1_5_2U1_2_1BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 1 5 2) (shape 1 2 1))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B1_5_2U1_2_1EOneD_sound B1_5_2U1_2_1ED_sound)
    (Ball.mul_sound B1_5_2U1_2_1D_sound logN2_sound)) (by decide +kernel)
lemma B1_5_2Binaries_sound (u : Shape) (hu : u ∈ (below (shape 1 5 2)).filter positive) :
    (B1_5_2Binaries u).Encloses ((fun u => binaryEntropyRate (binaryParameter (shape 1 5 2) u)) u) := by
  have hl : (below (shape 1 5 2)).filter positive = [(shape 1 1 2), (shape 1 2 1)] := by decide +kernel
  rw [hl] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl
  · exact B1_5_2U1_1_2BinaryEntropy_sound
  · exact B1_5_2U1_2_1BinaryEntropy_sound

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
lemma B1_5_2Btotal_sound_oai : B1_5_2Btotal.Encloses
    ((((below (shape 1 5 2)).filter positive).map (fun u => (littleMass (shape 1 5 2) u : ℝ) * (2 * Real.log 2 + binaryEntropyRate (binaryParameter (shape 1 5 2) u)))).sum) := by
  exact contains_sound (listSumBall_sound ((below (shape 1 5 2)).filter positive)
    (fun u => .mul (B1_5_2Masses u) (.add (.mul (.exact 2) logN2) (B1_5_2Binaries u))) _
    (fun u hu => Ball.mul_sound (B1_5_2Masses_sound u (List.mem_filter.mp hu).1)
      (Ball.add_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
        logN2_sound) (B1_5_2Binaries_sound u hu)))) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_5_2Btotal_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_5_2Btotal_sound_oai
