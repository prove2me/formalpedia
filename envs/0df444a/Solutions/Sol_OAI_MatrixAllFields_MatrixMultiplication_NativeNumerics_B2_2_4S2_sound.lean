-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_2_4S2_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:57:39.65361+00:00
-- url     : https://prove2.me/submissions/5f80bb3b-23a0-4154-859f-b6c3f7d05e59

import Mathlib
import Definitions.Def_OAIQ254M002
import Definitions.Def_OAIQ254M003
import Definitions.Def_OAIQ254M005
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_mul_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkLog_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B2_2_4Masses_sound
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
lemma logN5_sound : logN5.Encloses (Real.log ((5 : ℝ))) := by
  exact checkLog_sound logTwoBall_sound ((by convert Ball.exact_sound (5 : ℚ) using 1; norm_num)) (w := logN5Witness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma logN10_sound : logN10.Encloses (Real.log ((10 : ℝ))) := by
  exact checkLog_sound logTwoBall_sound ((by convert Ball.exact_sound (10 : ℚ) using 1; norm_num)) (w := logN10Witness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal2_2_4
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.bWeight_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inr _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inr
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
lemma B2_2_4_below : below (shape 2 2 4) = [
  (shape 0 0 4),
  (shape 0 1 3),
  (shape 0 2 2),
  (shape 1 0 3),
  (shape 1 1 2),
  (shape 1 2 1),
  (shape 2 0 2),
  (shape 2 1 1),
  (shape 2 2 0)] := by decide +kernel

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
lemma B2_2_4U0_0_4Leaf_sound : B2_2_4U0_0_4Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 2 4) (shape 0 0 4)) := by
  have hh : shapeMax (shape 0 0 4) = 4 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, ite_true, if_true]
  simpa only [B2_2_4U0_0_4Leaf, Ball.exact, Rat.cast_zero] using Ball.exact_sound 0
lemma B2_2_4U0_1_3Leaf_sound : B2_2_4U0_1_3Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 2 4) (shape 0 1 3)) := by
  have hh : shapeMax (shape 0 1 3) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, if_false, ite_true, if_true]
  exact logN10_sound
lemma B2_2_4U0_2_2D_sound : B2_2_4U0_2_2D.Encloses (binaryParameter (shape 2 2 4) (shape 0 2 2) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
lemma B2_2_4U0_2_2OneD_sound : B2_2_4U0_2_2OneD.Encloses (1 - (binaryParameter (shape 2 2 4) (shape 0 2 2) : ℝ)) := by
  have he : binaryParameter (shape 2 2 4) (shape 0 2 2) = (51781 / 500000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((448219 / 500000) : ℚ) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [B2_2_4U0_2_2OneD, Ball.exact])
lemma B2_2_4U0_2_2EDLog_sound : B2_2_4U0_2_2EDLog.Encloses (Real.log ((binaryParameter (shape 2 2 4) (shape 0 2 2) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B2_2_4U0_2_2D_sound) (w := B2_2_4U0_2_2EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma B2_2_4U0_2_2ED_sound : B2_2_4U0_2_2ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 2 2 4) (shape 0 2 2) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B2_2_4U0_2_2D_sound) B2_2_4U0_2_2EDLog_sound) (by decide +kernel)
lemma B2_2_4U0_2_2EOneDLog_sound : B2_2_4U0_2_2EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 2 2 4) (shape 0 2 2) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B2_2_4U0_2_2OneD_sound) (w := B2_2_4U0_2_2EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma B2_2_4U0_2_2EOneD_sound : B2_2_4U0_2_2EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 2 2 4) (shape 0 2 2) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B2_2_4U0_2_2OneD_sound) B2_2_4U0_2_2EOneDLog_sound) (by decide +kernel)
lemma B2_2_4U0_2_2BinaryEntropy_sound : B2_2_4U0_2_2BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 2 2 4) (shape 0 2 2))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B2_2_4U0_2_2EOneD_sound B2_2_4U0_2_2ED_sound)
    (Ball.mul_sound B2_2_4U0_2_2D_sound logN2_sound)) (by decide +kernel)
lemma B2_2_4U0_2_2Leaf_sound : B2_2_4U0_2_2Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 2 4) (shape 0 2 2)) := by
  have hh : shapeMax (shape 0 2 2) = 2 := by decide +kernel
  have hp : positive (shape 0 2 2) = false := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_false,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, if_false, ite_true, if_true]
  exact contains_sound (Ball.add_sound B2_2_4U0_2_2BinaryEntropy_sound
    (Ball.mul_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      B2_2_4U0_2_2OneD_sound) logN5_sound)) (by decide +kernel)
lemma B2_2_4U1_0_3Leaf_sound : B2_2_4U1_0_3Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 2 4) (shape 1 0 3)) := by
  have hh : shapeMax (shape 1 0 3) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, if_false, ite_true, if_true]
  exact logN10_sound
lemma B2_2_4U1_1_2Leaf_sound : B2_2_4U1_1_2Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 2 4) (shape 1 1 2)) := by
  have hh : shapeMax (shape 1 1 2) = 2 := by decide +kernel
  have hp : positive (shape 1 1 2) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, if_false]
  have ht : (Ball.exact (1990961 / 1000000)).Encloses (2 - (binaryParameter (shape 2 2 4) (shape 1 1 2) : ℝ)) := by
    have he : binaryParameter (shape 2 2 4) (shape 1 1 2) = (9039 / 1000000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((1990961 / 1000000) : ℚ) using 1
    all_goals try with_reducible_and_instances rfl
    norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
lemma B2_2_4U1_2_1Leaf_sound : B2_2_4U1_2_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 2 4) (shape 1 2 1)) := by
  have hh : shapeMax (shape 1 2 1) = 2 := by decide +kernel
  have hp : positive (shape 1 2 1) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, if_false]
  have ht : (Ball.exact (1957843 / 1000000)).Encloses (2 - (binaryParameter (shape 2 2 4) (shape 1 2 1) : ℝ)) := by
    have he : binaryParameter (shape 2 2 4) (shape 1 2 1) = (42157 / 1000000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((1957843 / 1000000) : ℚ) using 1
    all_goals try with_reducible_and_instances rfl
    norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
lemma B2_2_4U2_0_2D_sound : B2_2_4U2_0_2D.Encloses (binaryParameter (shape 2 2 4) (shape 2 0 2) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
lemma B2_2_4U2_0_2OneD_sound : B2_2_4U2_0_2OneD.Encloses (1 - (binaryParameter (shape 2 2 4) (shape 2 0 2) : ℝ)) := by
  have he : binaryParameter (shape 2 2 4) (shape 2 0 2) = (103577 / 1000000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((896423 / 1000000) : ℚ) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [B2_2_4U2_0_2OneD, Ball.exact])
lemma B2_2_4U2_0_2EDLog_sound : B2_2_4U2_0_2EDLog.Encloses (Real.log ((binaryParameter (shape 2 2 4) (shape 2 0 2) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B2_2_4U2_0_2D_sound) (w := B2_2_4U2_0_2EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma B2_2_4U2_0_2ED_sound : B2_2_4U2_0_2ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 2 2 4) (shape 2 0 2) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B2_2_4U2_0_2D_sound) B2_2_4U2_0_2EDLog_sound) (by decide +kernel)
lemma B2_2_4U2_0_2EOneDLog_sound : B2_2_4U2_0_2EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 2 2 4) (shape 2 0 2) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B2_2_4U2_0_2OneD_sound) (w := B2_2_4U2_0_2EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma B2_2_4U2_0_2EOneD_sound : B2_2_4U2_0_2EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 2 2 4) (shape 2 0 2) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B2_2_4U2_0_2OneD_sound) B2_2_4U2_0_2EOneDLog_sound) (by decide +kernel)
lemma B2_2_4U2_0_2BinaryEntropy_sound : B2_2_4U2_0_2BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 2 2 4) (shape 2 0 2))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B2_2_4U2_0_2EOneD_sound B2_2_4U2_0_2ED_sound)
    (Ball.mul_sound B2_2_4U2_0_2D_sound logN2_sound)) (by decide +kernel)
lemma B2_2_4U2_0_2Leaf_sound : B2_2_4U2_0_2Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 2 4) (shape 2 0 2)) := by
  have hh : shapeMax (shape 2 0 2) = 2 := by decide +kernel
  have hp : positive (shape 2 0 2) = false := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_false,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, if_false, ite_true, if_true]
  exact contains_sound (Ball.add_sound B2_2_4U2_0_2BinaryEntropy_sound
    (Ball.mul_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      B2_2_4U2_0_2OneD_sound) logN5_sound)) (by decide +kernel)
lemma B2_2_4U2_1_1Leaf_sound : B2_2_4U2_1_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 2 4) (shape 2 1 1)) := by
  have hh : shapeMax (shape 2 1 1) = 2 := by decide +kernel
  have hp : positive (shape 2 1 1) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, if_false]
  have ht : (Ball.exact (391567 / 200000)).Encloses (2 - (binaryParameter (shape 2 2 4) (shape 2 1 1) : ℝ)) := by
    have he : binaryParameter (shape 2 2 4) (shape 2 1 1) = (8433 / 200000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((391567 / 200000) : ℚ) using 1
    all_goals try with_reducible_and_instances rfl
    norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
lemma B2_2_4U2_2_0D_sound : B2_2_4U2_2_0D.Encloses (binaryParameter (shape 2 2 4) (shape 2 2 0) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
lemma B2_2_4U2_2_0OneD_sound : B2_2_4U2_2_0OneD.Encloses (1 - (binaryParameter (shape 2 2 4) (shape 2 2 0) : ℝ)) := by
  have he : binaryParameter (shape 2 2 4) (shape 2 2 0) = (31791 / 500000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((468209 / 500000) : ℚ) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [B2_2_4U2_2_0OneD, Ball.exact])
lemma B2_2_4U2_2_0EDLog_sound : B2_2_4U2_2_0EDLog.Encloses (Real.log ((binaryParameter (shape 2 2 4) (shape 2 2 0) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B2_2_4U2_2_0D_sound) (w := B2_2_4U2_2_0EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma B2_2_4U2_2_0ED_sound : B2_2_4U2_2_0ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 2 2 4) (shape 2 2 0) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B2_2_4U2_2_0D_sound) B2_2_4U2_2_0EDLog_sound) (by decide +kernel)
lemma B2_2_4U2_2_0EOneDLog_sound : B2_2_4U2_2_0EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 2 2 4) (shape 2 2 0) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B2_2_4U2_2_0OneD_sound) (w := B2_2_4U2_2_0EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma B2_2_4U2_2_0EOneD_sound : B2_2_4U2_2_0EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 2 2 4) (shape 2 2 0) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B2_2_4U2_2_0OneD_sound) B2_2_4U2_2_0EOneDLog_sound) (by decide +kernel)
lemma B2_2_4U2_2_0BinaryEntropy_sound : B2_2_4U2_2_0BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 2 2 4) (shape 2 2 0))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B2_2_4U2_2_0EOneD_sound B2_2_4U2_2_0ED_sound)
    (Ball.mul_sound B2_2_4U2_2_0D_sound logN2_sound)) (by decide +kernel)
lemma B2_2_4U2_2_0Leaf_sound : B2_2_4U2_2_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 2 4) (shape 2 2 0)) := by
  have hh : shapeMax (shape 2 2 0) = 2 := by decide +kernel
  have hp : positive (shape 2 2 0) = false := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_false,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, if_false, ite_true, if_true]
  exact contains_sound (Ball.add_sound B2_2_4U2_2_0BinaryEntropy_sound
    (Ball.mul_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      B2_2_4U2_2_0OneD_sound) logN5_sound)) (by decide +kernel)
lemma B2_2_4Leaves_sound (u : Shape) (hu : u ∈ below (shape 2 2 4)) :
    (B2_2_4Leaves u).Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 2 4) u) := by
  rw [B2_2_4_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B2_2_4U0_0_4Leaf_sound
  · exact B2_2_4U0_1_3Leaf_sound
  · exact B2_2_4U0_2_2Leaf_sound
  · exact B2_2_4U1_0_3Leaf_sound
  · exact B2_2_4U1_1_2Leaf_sound
  · exact B2_2_4U1_2_1Leaf_sound
  · exact B2_2_4U2_0_2Leaf_sound
  · exact B2_2_4U2_1_1Leaf_sound
  · exact B2_2_4U2_2_0Leaf_sound
lemma B2_2_4S2_sound_oai : B2_2_4S2.Encloses
    (((below (shape 2 2 4)).map fun u => (littleMass (shape 2 2 4) u : ℝ) * AllFieldTerminalRates.secondLeafRate (shape 2 2 4) u).sum) := by
  exact contains_sound (listSumBall_sound (below (shape 2 2 4))
    (fun u => .mul (B2_2_4Masses u) (B2_2_4Leaves u)) _
    (fun u hu => Ball.mul_sound (B2_2_4Masses_sound u hu) (B2_2_4Leaves_sound u hu))) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_2_4S2_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_2_4S2_sound_oai
