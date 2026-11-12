-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.nativeS2Ball_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:58:40.289662+00:00
-- url     : https://prove2.me/submissions/2369a7ee-3370-4126-9763-8f30b1b51534

import Mathlib
import Definitions.Def_OAIQ254M005
import Definitions.Def_OAIQ254M007
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_mul_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkLog_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B1_1_6S2_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B1_2_5Masses_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B1_3_4S2_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B1_4_3S2_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B1_5_2S2_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B1_6_1Masses_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B2_1_5Masses_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B2_2_4S2_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B2_3_3Masses_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B2_4_2S2_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B2_5_1S2_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B3_1_4S2_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B3_2_3S2_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B3_3_2S2_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B3_4_1Masses_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B4_1_3S2_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B4_2_2S2_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B4_3_1S2_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B5_1_2S2_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B5_2_1S2_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B6_1_1S2_sound
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
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitB2_3_3
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

lemma B2_3_3_below : below (shape 2 3 3) = [
  (shape 0 1 3),
  (shape 0 2 2),
  (shape 0 3 1),
  (shape 1 0 3),
  (shape 1 1 2),
  (shape 1 2 1),
  (shape 1 3 0),
  (shape 2 0 2),
  (shape 2 1 1),
  (shape 2 2 0)] := by decide +kernel

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
open AllFieldInitialEntropyCertificate
open scoped BigOperators
lemma B1_2_5_below : below (shape 1 2 5) = [
  (shape 0 0 4),
  (shape 0 1 3),
  (shape 0 2 2),
  (shape 1 0 3),
  (shape 1 1 2),
  (shape 1 2 1)] := by decide +kernel

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal1_2_5
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
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
lemma B1_2_5U0_0_4Leaf_sound : B1_2_5U0_0_4Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 2 5) (shape 0 0 4)) := by
  have hh : shapeMax (shape 0 0 4) = 4 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, ite_true, if_true]
  change (Ball.exact 0).Encloses 0
  simpa only [Rat.cast_zero] using Ball.exact_sound 0
lemma B1_2_5U0_1_3Leaf_sound : B1_2_5U0_1_3Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 2 5) (shape 0 1 3)) := by
  have hh : shapeMax (shape 0 1 3) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, if_false, ite_true, if_true]
  change logN10.Encloses (Real.log 10)
  exact logN10_sound
lemma B1_2_5U0_2_2D_sound : B1_2_5U0_2_2D.Encloses (binaryParameter (shape 1 2 5) (shape 0 2 2) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
lemma B1_2_5U0_2_2OneD_sound : B1_2_5U0_2_2OneD.Encloses (1 - (binaryParameter (shape 1 2 5) (shape 0 2 2) : ℝ)) := by
  have he : binaryParameter (shape 1 2 5) (shape 0 2 2) = (19531 / 200000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((180469 / 200000) : ℚ) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [B1_2_5U0_2_2OneD, Ball.exact])
lemma B1_2_5U0_2_2EDLog_sound : B1_2_5U0_2_2EDLog.Encloses (Real.log ((binaryParameter (shape 1 2 5) (shape 0 2 2) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B1_2_5U0_2_2D_sound) (w := B1_2_5U0_2_2EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma B1_2_5U0_2_2ED_sound : B1_2_5U0_2_2ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 1 2 5) (shape 0 2 2) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B1_2_5U0_2_2D_sound) B1_2_5U0_2_2EDLog_sound) (by decide +kernel)
lemma B1_2_5U0_2_2EOneDLog_sound : B1_2_5U0_2_2EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 1 2 5) (shape 0 2 2) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B1_2_5U0_2_2OneD_sound) (w := B1_2_5U0_2_2EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma B1_2_5U0_2_2EOneD_sound : B1_2_5U0_2_2EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 1 2 5) (shape 0 2 2) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B1_2_5U0_2_2OneD_sound) B1_2_5U0_2_2EOneDLog_sound) (by decide +kernel)
lemma B1_2_5U0_2_2BinaryEntropy_sound : B1_2_5U0_2_2BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 1 2 5) (shape 0 2 2))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B1_2_5U0_2_2EOneD_sound B1_2_5U0_2_2ED_sound)
    (Ball.mul_sound B1_2_5U0_2_2D_sound logN2_sound)) (by decide +kernel)
lemma B1_2_5U0_2_2Leaf_sound : B1_2_5U0_2_2Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 2 5) (shape 0 2 2)) := by
  have hh : shapeMax (shape 0 2 2) = 2 := by decide +kernel
  have hp : positive (shape 0 2 2) = false := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_false,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, if_false, ite_true, if_true]
  exact contains_sound (Ball.add_sound B1_2_5U0_2_2BinaryEntropy_sound
    (Ball.mul_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      B1_2_5U0_2_2OneD_sound) logN5_sound)) (by decide +kernel)
lemma B1_2_5U1_0_3Leaf_sound : B1_2_5U1_0_3Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 2 5) (shape 1 0 3)) := by
  have hh : shapeMax (shape 1 0 3) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, if_false, ite_true, if_true]
  change logN10.Encloses (Real.log 10)
  exact logN10_sound
lemma B1_2_5U1_1_2Leaf_sound : B1_2_5U1_1_2Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 2 5) (shape 1 1 2)) := by
  have hh : shapeMax (shape 1 1 2) = 2 := by decide +kernel
  have hp : positive (shape 1 1 2) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, if_false]
  have ht : (Ball.exact 2).Encloses (2 - (binaryParameter (shape 1 2 5) (shape 1 1 2) : ℝ)) := by
    have he : binaryParameter (shape 1 2 5) (shape 1 1 2) = 0 := by decide +kernel
    rw [he]
    convert Ball.exact_sound (2 : ℚ) using 1
    all_goals try with_reducible_and_instances rfl
    norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
lemma B1_2_5U1_2_1Leaf_sound : B1_2_5U1_2_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 2 5) (shape 1 2 1)) := by
  have hh : shapeMax (shape 1 2 1) = 2 := by decide +kernel
  have hp : positive (shape 1 2 1) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, if_false]
  have ht : (Ball.exact (489467 / 250000)).Encloses (2 - (binaryParameter (shape 1 2 5) (shape 1 2 1) : ℝ)) := by
    have he : binaryParameter (shape 1 2 5) (shape 1 2 1) = (10533 / 250000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((489467 / 250000) : ℚ) using 1
    all_goals try with_reducible_and_instances rfl
    norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
lemma B1_2_5Leaves_sound (u : Shape) (hu : u ∈ below (shape 1 2 5)) :
    (B1_2_5Leaves u).Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 2 5) u) := by
  rw [B1_2_5_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · exact B1_2_5U0_0_4Leaf_sound
  · exact B1_2_5U0_1_3Leaf_sound
  · exact B1_2_5U0_2_2Leaf_sound
  · exact B1_2_5U1_0_3Leaf_sound
  · exact B1_2_5U1_1_2Leaf_sound
  · exact B1_2_5U1_2_1Leaf_sound
lemma B1_2_5S2_sound : B1_2_5S2.Encloses
    (((below (shape 1 2 5)).map fun u => (littleMass (shape 1 2 5) u : ℝ) * AllFieldTerminalRates.secondLeafRate (shape 1 2 5) u).sum) := by
  exact contains_sound (listSumBall_sound (below (shape 1 2 5))
    (fun u => .mul (B1_2_5Masses u) (B1_2_5Leaves u)) _
    (fun u hu => Ball.mul_sound (B1_2_5Masses_sound u hu) (B1_2_5Leaves_sound u hu))) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal1_6_1
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
lemma B1_6_1_below : below (shape 1 6 1) = [
  (shape 0 3 1),
  (shape 0 4 0),
  (shape 1 2 1),
  (shape 1 3 0)] := by decide +kernel

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
lemma B1_6_1U0_3_1Leaf_sound : B1_6_1U0_3_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 6 1) (shape 0 3 1)) := by
  have hh : shapeMax (shape 0 3 1) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, if_false, ite_true, if_true]
  exact logN10_sound
lemma B1_6_1U0_4_0Leaf_sound : B1_6_1U0_4_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 6 1) (shape 0 4 0)) := by
  have hh : shapeMax (shape 0 4 0) = 4 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, ite_true, if_true]
  simpa only [B1_6_1U0_4_0Leaf, Ball.exact, Rat.cast_zero] using Ball.exact_sound 0
lemma B1_6_1U1_2_1Leaf_sound : B1_6_1U1_2_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 6 1) (shape 1 2 1)) := by
  have hh : shapeMax (shape 1 2 1) = 2 := by decide +kernel
  have hp : positive (shape 1 2 1) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, if_false]
  have ht : (Ball.exact (1958009 / 1000000)).Encloses (2 - (binaryParameter (shape 1 6 1) (shape 1 2 1) : ℝ)) := by
    have he : binaryParameter (shape 1 6 1) (shape 1 2 1) = (41991 / 1000000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((1958009 / 1000000) : ℚ) using 1
    all_goals try with_reducible_and_instances rfl
    norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
lemma B1_6_1U1_3_0Leaf_sound : B1_6_1U1_3_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 6 1) (shape 1 3 0)) := by
  have hh : shapeMax (shape 1 3 0) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, if_false, ite_true, if_true]
  exact logN10_sound
lemma B1_6_1Leaves_sound (u : Shape) (hu : u ∈ below (shape 1 6 1)) :
    (B1_6_1Leaves u).Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 6 1) u) := by
  rw [B1_6_1_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl
  · exact B1_6_1U0_3_1Leaf_sound
  · exact B1_6_1U0_4_0Leaf_sound
  · exact B1_6_1U1_2_1Leaf_sound
  · exact B1_6_1U1_3_0Leaf_sound
lemma B1_6_1S2_sound : B1_6_1S2.Encloses
    (((below (shape 1 6 1)).map fun u => (littleMass (shape 1 6 1) u : ℝ) * AllFieldTerminalRates.secondLeafRate (shape 1 6 1) u).sum) := by
  exact contains_sound (listSumBall_sound (below (shape 1 6 1))
    (fun u => .mul (B1_6_1Masses u) (B1_6_1Leaves u)) _
    (fun u hu => Ball.mul_sound (B1_6_1Masses_sound u hu) (B1_6_1Leaves_sound u hu))) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal2_1_5
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
lemma B2_1_5_below : below (shape 2 1 5) = [
  (shape 0 0 4),
  (shape 0 1 3),
  (shape 1 0 3),
  (shape 1 1 2),
  (shape 2 0 2),
  (shape 2 1 1)] := by decide +kernel

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
lemma B2_1_5U0_0_4Leaf_sound : B2_1_5U0_0_4Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 1 5) (shape 0 0 4)) := by
  have hh : shapeMax (shape 0 0 4) = 4 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, ite_true, if_true]
  simpa only [B2_1_5U0_0_4Leaf, Ball.exact, Rat.cast_zero] using Ball.exact_sound 0
lemma B2_1_5U0_1_3Leaf_sound : B2_1_5U0_1_3Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 1 5) (shape 0 1 3)) := by
  have hh : shapeMax (shape 0 1 3) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, if_false, ite_true, if_true]
  exact logN10_sound
lemma B2_1_5U1_0_3Leaf_sound : B2_1_5U1_0_3Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 1 5) (shape 1 0 3)) := by
  have hh : shapeMax (shape 1 0 3) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, if_false, ite_true, if_true]
  exact logN10_sound
lemma B2_1_5U1_1_2Leaf_sound : B2_1_5U1_1_2Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 1 5) (shape 1 1 2)) := by
  have hh : shapeMax (shape 1 1 2) = 2 := by decide +kernel
  have hp : positive (shape 1 1 2) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, if_false]
  have ht : (Ball.exact (1999999 / 1000000)).Encloses (2 - (binaryParameter (shape 2 1 5) (shape 1 1 2) : ℝ)) := by
    have he : binaryParameter (shape 2 1 5) (shape 1 1 2) = (1 / 1000000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((1999999 / 1000000) : ℚ) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [Ball.exact])
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
lemma B2_1_5U2_0_2D_sound : B2_1_5U2_0_2D.Encloses (binaryParameter (shape 2 1 5) (shape 2 0 2) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
lemma B2_1_5U2_0_2OneD_sound : B2_1_5U2_0_2OneD.Encloses (1 - (binaryParameter (shape 2 1 5) (shape 2 0 2) : ℝ)) := by
  have he : binaryParameter (shape 2 1 5) (shape 2 0 2) = (50311 / 500000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((449689 / 500000) : ℚ) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [B2_1_5U2_0_2OneD, Ball.exact])
lemma B2_1_5U2_0_2EDLog_sound : B2_1_5U2_0_2EDLog.Encloses (Real.log ((binaryParameter (shape 2 1 5) (shape 2 0 2) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B2_1_5U2_0_2D_sound) (w := B2_1_5U2_0_2EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma B2_1_5U2_0_2ED_sound : B2_1_5U2_0_2ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 2 1 5) (shape 2 0 2) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B2_1_5U2_0_2D_sound) B2_1_5U2_0_2EDLog_sound) (by decide +kernel)
lemma B2_1_5U2_0_2EOneDLog_sound : B2_1_5U2_0_2EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 2 1 5) (shape 2 0 2) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B2_1_5U2_0_2OneD_sound) (w := B2_1_5U2_0_2EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma B2_1_5U2_0_2EOneD_sound : B2_1_5U2_0_2EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 2 1 5) (shape 2 0 2) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B2_1_5U2_0_2OneD_sound) B2_1_5U2_0_2EOneDLog_sound) (by decide +kernel)
lemma B2_1_5U2_0_2BinaryEntropy_sound : B2_1_5U2_0_2BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 2 1 5) (shape 2 0 2))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B2_1_5U2_0_2EOneD_sound B2_1_5U2_0_2ED_sound)
    (Ball.mul_sound B2_1_5U2_0_2D_sound logN2_sound)) (by decide +kernel)
lemma B2_1_5U2_0_2Leaf_sound : B2_1_5U2_0_2Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 1 5) (shape 2 0 2)) := by
  have hh : shapeMax (shape 2 0 2) = 2 := by decide +kernel
  have hp : positive (shape 2 0 2) = false := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_false,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, if_false, ite_true, if_true]
  exact contains_sound (Ball.add_sound B2_1_5U2_0_2BinaryEntropy_sound
    (Ball.mul_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      B2_1_5U2_0_2OneD_sound) logN5_sound)) (by decide +kernel)
lemma B2_1_5U2_1_1Leaf_sound : B2_1_5U2_1_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 1 5) (shape 2 1 1)) := by
  have hh : shapeMax (shape 2 1 1) = 2 := by decide +kernel
  have hp : positive (shape 2 1 1) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, if_false]
  have ht : (Ball.exact (978917 / 500000)).Encloses (2 - (binaryParameter (shape 2 1 5) (shape 2 1 1) : ℝ)) := by
    have he : binaryParameter (shape 2 1 5) (shape 2 1 1) = (21083 / 500000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((978917 / 500000) : ℚ) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [Ball.exact])
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
lemma B2_1_5Leaves_sound (u : Shape) (hu : u ∈ below (shape 2 1 5)) :
    (B2_1_5Leaves u).Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 1 5) u) := by
  rw [B2_1_5_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · exact B2_1_5U0_0_4Leaf_sound
  · exact B2_1_5U0_1_3Leaf_sound
  · exact B2_1_5U1_0_3Leaf_sound
  · exact B2_1_5U1_1_2Leaf_sound
  · exact B2_1_5U2_0_2Leaf_sound
  · exact B2_1_5U2_1_1Leaf_sound
lemma B2_1_5S2_sound : B2_1_5S2.Encloses
    (((below (shape 2 1 5)).map fun u => (littleMass (shape 2 1 5) u : ℝ) * AllFieldTerminalRates.secondLeafRate (shape 2 1 5) u).sum) := by
  exact contains_sound (listSumBall_sound (below (shape 2 1 5))
    (fun u => .mul (B2_1_5Masses u) (B2_1_5Leaves u)) _
    (fun u hu => Ball.mul_sound (B2_1_5Masses_sound u hu) (B2_1_5Leaves_sound u hu))) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal2_3_3
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
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
lemma B2_3_3U0_1_3Leaf_sound : B2_3_3U0_1_3Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 3 3) (shape 0 1 3)) := by
  have hh : shapeMax (shape 0 1 3) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, if_false, ite_true, if_true]
  exact logN10_sound
lemma B2_3_3U0_2_2D_sound : B2_3_3U0_2_2D.Encloses (binaryParameter (shape 2 3 3) (shape 0 2 2) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
lemma B2_3_3U0_2_2OneD_sound : B2_3_3U0_2_2OneD.Encloses (1 - (binaryParameter (shape 2 3 3) (shape 0 2 2) : ℝ)) := by
  have he : binaryParameter (shape 2 3 3) (shape 0 2 2) = (55041 / 500000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((444959 / 500000) : ℚ) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [B2_3_3U0_2_2OneD, Ball.exact])
lemma B2_3_3U0_2_2EDLog_sound : B2_3_3U0_2_2EDLog.Encloses (Real.log ((binaryParameter (shape 2 3 3) (shape 0 2 2) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B2_3_3U0_2_2D_sound) (w := B2_3_3U0_2_2EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma B2_3_3U0_2_2ED_sound : B2_3_3U0_2_2ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 2 3 3) (shape 0 2 2) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B2_3_3U0_2_2D_sound) B2_3_3U0_2_2EDLog_sound) (by decide +kernel)
lemma B2_3_3U0_2_2EOneDLog_sound : B2_3_3U0_2_2EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 2 3 3) (shape 0 2 2) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B2_3_3U0_2_2OneD_sound) (w := B2_3_3U0_2_2EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma B2_3_3U0_2_2EOneD_sound : B2_3_3U0_2_2EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 2 3 3) (shape 0 2 2) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B2_3_3U0_2_2OneD_sound) B2_3_3U0_2_2EOneDLog_sound) (by decide +kernel)
lemma B2_3_3U0_2_2BinaryEntropy_sound : B2_3_3U0_2_2BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 2 3 3) (shape 0 2 2))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B2_3_3U0_2_2EOneD_sound B2_3_3U0_2_2ED_sound)
    (Ball.mul_sound B2_3_3U0_2_2D_sound logN2_sound)) (by decide +kernel)
lemma B2_3_3U0_2_2Leaf_sound : B2_3_3U0_2_2Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 3 3) (shape 0 2 2)) := by
  have hh : shapeMax (shape 0 2 2) = 2 := by decide +kernel
  have hp : positive (shape 0 2 2) = false := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_false,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, if_false, ite_true, if_true]
  exact contains_sound (Ball.add_sound B2_3_3U0_2_2BinaryEntropy_sound
    (Ball.mul_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      B2_3_3U0_2_2OneD_sound) logN5_sound)) (by decide +kernel)
lemma B2_3_3U0_3_1Leaf_sound : B2_3_3U0_3_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 3 3) (shape 0 3 1)) := by
  have hh : shapeMax (shape 0 3 1) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, if_false, ite_true, if_true]
  exact logN10_sound
lemma B2_3_3U1_0_3Leaf_sound : B2_3_3U1_0_3Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 3 3) (shape 1 0 3)) := by
  have hh : shapeMax (shape 1 0 3) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, if_false, ite_true, if_true]
  exact logN10_sound
lemma B2_3_3U1_1_2Leaf_sound : B2_3_3U1_1_2Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 3 3) (shape 1 1 2)) := by
  have hh : shapeMax (shape 1 1 2) = 2 := by decide +kernel
  have hp : positive (shape 1 1 2) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, if_false]
  have ht : (Ball.exact (249427 / 125000)).Encloses (2 - (binaryParameter (shape 2 3 3) (shape 1 1 2) : ℝ)) := by
    have he : binaryParameter (shape 2 3 3) (shape 1 1 2) = (573 / 125000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((249427 / 125000) : ℚ) using 1
    all_goals try with_reducible_and_instances rfl
    norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
lemma B2_3_3U1_2_1Leaf_sound : B2_3_3U1_2_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 3 3) (shape 1 2 1)) := by
  have hh : shapeMax (shape 1 2 1) = 2 := by decide +kernel
  have hp : positive (shape 1 2 1) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, if_false]
  have ht : (Ball.exact (78313 / 40000)).Encloses (2 - (binaryParameter (shape 2 3 3) (shape 1 2 1) : ℝ)) := by
    have he : binaryParameter (shape 2 3 3) (shape 1 2 1) = (1687 / 40000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((78313 / 40000) : ℚ) using 1
    all_goals try with_reducible_and_instances rfl
    norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
lemma B2_3_3U1_3_0Leaf_sound : B2_3_3U1_3_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 3 3) (shape 1 3 0)) := by
  have hh : shapeMax (shape 1 3 0) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, if_false, ite_true, if_true]
  exact logN10_sound
lemma B2_3_3U2_0_2D_sound : B2_3_3U2_0_2D.Encloses (binaryParameter (shape 2 3 3) (shape 2 0 2) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
lemma B2_3_3U2_0_2OneD_sound : B2_3_3U2_0_2OneD.Encloses (1 - (binaryParameter (shape 2 3 3) (shape 2 0 2) : ℝ)) := by
  have he : binaryParameter (shape 2 3 3) (shape 2 0 2) = (104091 / 1000000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((895909 / 1000000) : ℚ) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [B2_3_3U2_0_2OneD, Ball.exact])
lemma B2_3_3U2_0_2EDLog_sound : B2_3_3U2_0_2EDLog.Encloses (Real.log ((binaryParameter (shape 2 3 3) (shape 2 0 2) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B2_3_3U2_0_2D_sound) (w := B2_3_3U2_0_2EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma B2_3_3U2_0_2ED_sound : B2_3_3U2_0_2ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 2 3 3) (shape 2 0 2) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B2_3_3U2_0_2D_sound) B2_3_3U2_0_2EDLog_sound) (by decide +kernel)
lemma B2_3_3U2_0_2EOneDLog_sound : B2_3_3U2_0_2EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 2 3 3) (shape 2 0 2) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B2_3_3U2_0_2OneD_sound) (w := B2_3_3U2_0_2EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma B2_3_3U2_0_2EOneD_sound : B2_3_3U2_0_2EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 2 3 3) (shape 2 0 2) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B2_3_3U2_0_2OneD_sound) B2_3_3U2_0_2EOneDLog_sound) (by decide +kernel)
lemma B2_3_3U2_0_2BinaryEntropy_sound : B2_3_3U2_0_2BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 2 3 3) (shape 2 0 2))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B2_3_3U2_0_2EOneD_sound B2_3_3U2_0_2ED_sound)
    (Ball.mul_sound B2_3_3U2_0_2D_sound logN2_sound)) (by decide +kernel)
lemma B2_3_3U2_0_2Leaf_sound : B2_3_3U2_0_2Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 3 3) (shape 2 0 2)) := by
  have hh : shapeMax (shape 2 0 2) = 2 := by decide +kernel
  have hp : positive (shape 2 0 2) = false := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_false,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, if_false, ite_true, if_true]
  exact contains_sound (Ball.add_sound B2_3_3U2_0_2BinaryEntropy_sound
    (Ball.mul_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      B2_3_3U2_0_2OneD_sound) logN5_sound)) (by decide +kernel)
lemma B2_3_3U2_1_1Leaf_sound : B2_3_3U2_1_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 3 3) (shape 2 1 1)) := by
  have hh : shapeMax (shape 2 1 1) = 2 := by decide +kernel
  have hp : positive (shape 2 1 1) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, if_false]
  have ht : (Ball.exact (980581 / 500000)).Encloses (2 - (binaryParameter (shape 2 3 3) (shape 2 1 1) : ℝ)) := by
    have he : binaryParameter (shape 2 3 3) (shape 2 1 1) = (19419 / 500000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((980581 / 500000) : ℚ) using 1
    all_goals try with_reducible_and_instances rfl
    norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
lemma B2_3_3U2_2_0D_sound : B2_3_3U2_2_0D.Encloses (binaryParameter (shape 2 3 3) (shape 2 2 0) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
lemma B2_3_3U2_2_0OneD_sound : B2_3_3U2_2_0OneD.Encloses (1 - (binaryParameter (shape 2 3 3) (shape 2 2 0) : ℝ)) := by
  have he : binaryParameter (shape 2 3 3) (shape 2 2 0) = (102383 / 1000000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((897617 / 1000000) : ℚ) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [B2_3_3U2_2_0OneD, Ball.exact])
lemma B2_3_3U2_2_0EDLog_sound : B2_3_3U2_2_0EDLog.Encloses (Real.log ((binaryParameter (shape 2 3 3) (shape 2 2 0) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B2_3_3U2_2_0D_sound) (w := B2_3_3U2_2_0EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma B2_3_3U2_2_0ED_sound : B2_3_3U2_2_0ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 2 3 3) (shape 2 2 0) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B2_3_3U2_2_0D_sound) B2_3_3U2_2_0EDLog_sound) (by decide +kernel)
lemma B2_3_3U2_2_0EOneDLog_sound : B2_3_3U2_2_0EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 2 3 3) (shape 2 2 0) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B2_3_3U2_2_0OneD_sound) (w := B2_3_3U2_2_0EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma B2_3_3U2_2_0EOneD_sound : B2_3_3U2_2_0EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 2 3 3) (shape 2 2 0) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B2_3_3U2_2_0OneD_sound) B2_3_3U2_2_0EOneDLog_sound) (by decide +kernel)
lemma B2_3_3U2_2_0BinaryEntropy_sound : B2_3_3U2_2_0BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 2 3 3) (shape 2 2 0))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B2_3_3U2_2_0EOneD_sound B2_3_3U2_2_0ED_sound)
    (Ball.mul_sound B2_3_3U2_2_0D_sound logN2_sound)) (by decide +kernel)
lemma B2_3_3U2_2_0Leaf_sound : B2_3_3U2_2_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 3 3) (shape 2 2 0)) := by
  have hh : shapeMax (shape 2 2 0) = 2 := by decide +kernel
  have hp : positive (shape 2 2 0) = false := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_false,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, if_false, ite_true, if_true]
  exact contains_sound (Ball.add_sound B2_3_3U2_2_0BinaryEntropy_sound
    (Ball.mul_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      B2_3_3U2_2_0OneD_sound) logN5_sound)) (by decide +kernel)
lemma B2_3_3Leaves_sound (u : Shape) (hu : u ∈ below (shape 2 3 3)) :
    (B2_3_3Leaves u).Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 3 3) u) := by
  rw [B2_3_3_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B2_3_3U0_1_3Leaf_sound
  · exact B2_3_3U0_2_2Leaf_sound
  · exact B2_3_3U0_3_1Leaf_sound
  · exact B2_3_3U1_0_3Leaf_sound
  · exact B2_3_3U1_1_2Leaf_sound
  · exact B2_3_3U1_2_1Leaf_sound
  · exact B2_3_3U1_3_0Leaf_sound
  · exact B2_3_3U2_0_2Leaf_sound
  · exact B2_3_3U2_1_1Leaf_sound
  · exact B2_3_3U2_2_0Leaf_sound
lemma B2_3_3S2_sound : B2_3_3S2.Encloses
    (((below (shape 2 3 3)).map fun u => (littleMass (shape 2 3 3) u : ℝ) * AllFieldTerminalRates.secondLeafRate (shape 2 3 3) u).sum) := by
  exact contains_sound (listSumBall_sound (below (shape 2 3 3))
    (fun u => .mul (B2_3_3Masses u) (B2_3_3Leaves u)) _
    (fun u hu => Ball.mul_sound (B2_3_3Masses_sound u hu) (B2_3_3Leaves_sound u hu))) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal3_4_1
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
lemma B3_4_1_below : below (shape 3 4 1) = [
  (shape 0 3 1),
  (shape 0 4 0),
  (shape 1 2 1),
  (shape 1 3 0),
  (shape 2 1 1),
  (shape 2 2 0),
  (shape 3 0 1),
  (shape 3 1 0)] := by decide +kernel

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
lemma B3_4_1U0_3_1Leaf_sound : B3_4_1U0_3_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 4 1) (shape 0 3 1)) := by
  have hh : shapeMax (shape 0 3 1) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, if_false, ite_true, if_true]
  change logN10.Encloses (Real.log 10)
  exact logN10_sound
lemma B3_4_1U0_4_0Leaf_sound : B3_4_1U0_4_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 4 1) (shape 0 4 0)) := by
  have hh : shapeMax (shape 0 4 0) = 4 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, ite_true, if_true]
  change (Ball.exact 0).Encloses 0
  simpa only [Rat.cast_zero] using Ball.exact_sound 0
lemma B3_4_1U1_2_1Leaf_sound : B3_4_1U1_2_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 4 1) (shape 1 2 1)) := by
  have hh : shapeMax (shape 1 2 1) = 2 := by decide +kernel
  have hp : positive (shape 1 2 1) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, if_false]
  have ht : (Ball.exact (1997047 / 1000000)).Encloses (2 - (binaryParameter (shape 3 4 1) (shape 1 2 1) : ℝ)) := by
    have he : binaryParameter (shape 3 4 1) (shape 1 2 1) = (2953 / 1000000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((1997047 / 1000000) : ℚ) using 1
    all_goals try with_reducible_and_instances rfl
    norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
lemma B3_4_1U1_3_0Leaf_sound : B3_4_1U1_3_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 4 1) (shape 1 3 0)) := by
  have hh : shapeMax (shape 1 3 0) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, if_false, ite_true, if_true]
  change logN10.Encloses (Real.log 10)
  exact logN10_sound
lemma B3_4_1U2_1_1Leaf_sound : B3_4_1U2_1_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 4 1) (shape 2 1 1)) := by
  have hh : shapeMax (shape 2 1 1) = 2 := by decide +kernel
  have hp : positive (shape 2 1 1) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, if_false]
  have ht : (Ball.exact (978917 / 500000)).Encloses (2 - (binaryParameter (shape 3 4 1) (shape 2 1 1) : ℝ)) := by
    have he : binaryParameter (shape 3 4 1) (shape 2 1 1) = (21083 / 500000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((978917 / 500000) : ℚ) using 1
    all_goals try with_reducible_and_instances rfl
    norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
lemma B3_4_1U2_2_0D_sound : B3_4_1U2_2_0D.Encloses (binaryParameter (shape 3 4 1) (shape 2 2 0) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
lemma B3_4_1U2_2_0OneD_sound : B3_4_1U2_2_0OneD.Encloses (1 - (binaryParameter (shape 3 4 1) (shape 2 2 0) : ℝ)) := by
  have he : binaryParameter (shape 3 4 1) (shape 2 2 0) = (12 / 125) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((113 / 125) : ℚ) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [B3_4_1U2_2_0OneD, Ball.exact])
lemma B3_4_1U2_2_0EDLog_sound : B3_4_1U2_2_0EDLog.Encloses (Real.log ((binaryParameter (shape 3 4 1) (shape 2 2 0) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B3_4_1U2_2_0D_sound) (w := B3_4_1U2_2_0EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma B3_4_1U2_2_0ED_sound : B3_4_1U2_2_0ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 3 4 1) (shape 2 2 0) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B3_4_1U2_2_0D_sound) B3_4_1U2_2_0EDLog_sound) (by decide +kernel)
lemma B3_4_1U2_2_0EOneDLog_sound : B3_4_1U2_2_0EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 3 4 1) (shape 2 2 0) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B3_4_1U2_2_0OneD_sound) (w := B3_4_1U2_2_0EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma B3_4_1U2_2_0EOneD_sound : B3_4_1U2_2_0EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 3 4 1) (shape 2 2 0) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B3_4_1U2_2_0OneD_sound) B3_4_1U2_2_0EOneDLog_sound) (by decide +kernel)
lemma B3_4_1U2_2_0BinaryEntropy_sound : B3_4_1U2_2_0BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 3 4 1) (shape 2 2 0))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B3_4_1U2_2_0EOneD_sound B3_4_1U2_2_0ED_sound)
    (Ball.mul_sound B3_4_1U2_2_0D_sound logN2_sound)) (by decide +kernel)
lemma B3_4_1U2_2_0Leaf_sound : B3_4_1U2_2_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 4 1) (shape 2 2 0)) := by
  have hh : shapeMax (shape 2 2 0) = 2 := by decide +kernel
  have hp : positive (shape 2 2 0) = false := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_false,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, if_false, ite_true, if_true]
  exact contains_sound (Ball.add_sound B3_4_1U2_2_0BinaryEntropy_sound
    (Ball.mul_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      B3_4_1U2_2_0OneD_sound) logN5_sound)) (by decide +kernel)
lemma B3_4_1U3_0_1Leaf_sound : B3_4_1U3_0_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 4 1) (shape 3 0 1)) := by
  have hh : shapeMax (shape 3 0 1) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, if_false, ite_true, if_true]
  change logN10.Encloses (Real.log 10)
  exact logN10_sound
lemma B3_4_1U3_1_0Leaf_sound : B3_4_1U3_1_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 4 1) (shape 3 1 0)) := by
  have hh : shapeMax (shape 3 1 0) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, if_false, ite_true, if_true]
  change logN10.Encloses (Real.log 10)
  exact logN10_sound
lemma B3_4_1Leaves_sound (u : Shape) (hu : u ∈ below (shape 3 4 1)) :
    (B3_4_1Leaves u).Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 4 1) u) := by
  rw [B3_4_1_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B3_4_1U0_3_1Leaf_sound
  · exact B3_4_1U0_4_0Leaf_sound
  · exact B3_4_1U1_2_1Leaf_sound
  · exact B3_4_1U1_3_0Leaf_sound
  · exact B3_4_1U2_1_1Leaf_sound
  · exact B3_4_1U2_2_0Leaf_sound
  · exact B3_4_1U3_0_1Leaf_sound
  · exact B3_4_1U3_1_0Leaf_sound
lemma B3_4_1S2_sound : B3_4_1S2.Encloses
    (((below (shape 3 4 1)).map fun u => (littleMass (shape 3 4 1) u : ℝ) * AllFieldTerminalRates.secondLeafRate (shape 3 4 1) u).sum) := by
  exact contains_sound (listSumBall_sound (below (shape 3 4 1))
    (fun u => .mul (B3_4_1Masses u) (B3_4_1Leaves u)) _
    (fun u hu => Ball.mul_sound (B3_4_1Masses_sound u hu) (B3_4_1Leaves_sound u hu))) (by decide +kernel)

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
open AllFieldTerminalRates AllFieldVolumeCertificate
lemma s2ParentBalls_sound (t : Shape) (ht : t ∈ positiveSecond) :
    (s2ParentBalls t).Encloses (((below t).map fun u =>
      (littleMass t u : ℝ) * secondLeafRate t u).sum) := by
  rw [positiveSecond_list] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B1_1_6S2_sound
  · exact B1_2_5S2_sound
  · exact B1_3_4S2_sound
  · exact B1_4_3S2_sound
  · exact B1_5_2S2_sound
  · exact B1_6_1S2_sound
  · exact B2_1_5S2_sound
  · exact B2_2_4S2_sound
  · exact B2_3_3S2_sound
  · exact B2_4_2S2_sound
  · exact B2_5_1S2_sound
  · exact B3_1_4S2_sound
  · exact B3_2_3S2_sound
  · exact B3_3_2S2_sound
  · exact B3_4_1S2_sound
  · exact B4_1_3S2_sound
  · exact B4_2_2S2_sound
  · exact B4_3_1S2_sound
  · exact B5_1_2S2_sound
  · exact B5_2_1S2_sound
  · exact B6_1_1S2_sound
lemma nativeS2Ball_sound_oai : nativeS2Ball.Encloses S2 := by
  exact contains_sound (listSumBall_sound positiveSecond s2ParentBalls _
    s2ParentBalls_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.nativeS2Ball_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.nativeS2Ball_sound_oai
