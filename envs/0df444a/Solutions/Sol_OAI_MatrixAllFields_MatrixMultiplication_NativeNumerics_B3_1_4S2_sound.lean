-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_1_4S2_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:58:27.197687+00:00
-- url     : https://prove2.me/submissions/ca99aced-847b-4c5e-954e-867adc987ea7

import Mathlib
import Definitions.Def_OAIQ254M002
import Definitions.Def_OAIQ254M003
import Definitions.Def_OAIQ254M005
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_mul_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkLog_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B3_1_4Masses_sound
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
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal3_1_4
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
lemma B3_1_4_below : below (shape 3 1 4) = [
  (shape 0 0 4),
  (shape 0 1 3),
  (shape 1 0 3),
  (shape 1 1 2),
  (shape 2 0 2),
  (shape 2 1 1),
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
lemma B3_1_4U0_0_4Leaf_sound : B3_1_4U0_0_4Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 1 4) (shape 0 0 4)) := by
  have hh : shapeMax (shape 0 0 4) = 4 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, ite_true, if_true]
  simpa only [B3_1_4U0_0_4Leaf, Ball.exact, Rat.cast_zero] using Ball.exact_sound 0
lemma B3_1_4U0_1_3Leaf_sound : B3_1_4U0_1_3Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 1 4) (shape 0 1 3)) := by
  have hh : shapeMax (shape 0 1 3) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, if_false, ite_true, if_true]
  exact logN10_sound
lemma B3_1_4U1_0_3Leaf_sound : B3_1_4U1_0_3Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 1 4) (shape 1 0 3)) := by
  have hh : shapeMax (shape 1 0 3) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, if_false, ite_true, if_true]
  exact logN10_sound
lemma B3_1_4U1_1_2Leaf_sound : B3_1_4U1_1_2Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 1 4) (shape 1 1 2)) := by
  have hh : shapeMax (shape 1 1 2) = 2 := by decide +kernel
  have hp : positive (shape 1 1 2) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, if_false]
  have ht : (Ball.exact (1997793 / 1000000)).Encloses (2 - (binaryParameter (shape 3 1 4) (shape 1 1 2) : ℝ)) := by
    have he : binaryParameter (shape 3 1 4) (shape 1 1 2) = (2207 / 1000000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((1997793 / 1000000) : ℚ) using 1
    all_goals try with_reducible_and_instances rfl
    norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
lemma B3_1_4U2_0_2D_sound : B3_1_4U2_0_2D.Encloses (binaryParameter (shape 3 1 4) (shape 2 0 2) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
lemma B3_1_4U2_0_2OneD_sound : B3_1_4U2_0_2OneD.Encloses (1 - (binaryParameter (shape 3 1 4) (shape 2 0 2) : ℝ)) := by
  have he : binaryParameter (shape 3 1 4) (shape 2 0 2) = (5923 / 62500) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((56577 / 62500) : ℚ) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [B3_1_4U2_0_2OneD, Ball.exact])
lemma B3_1_4U2_0_2EDLog_sound : B3_1_4U2_0_2EDLog.Encloses (Real.log ((binaryParameter (shape 3 1 4) (shape 2 0 2) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B3_1_4U2_0_2D_sound) (w := B3_1_4U2_0_2EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma B3_1_4U2_0_2ED_sound : B3_1_4U2_0_2ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 3 1 4) (shape 2 0 2) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B3_1_4U2_0_2D_sound) B3_1_4U2_0_2EDLog_sound) (by decide +kernel)
lemma B3_1_4U2_0_2EOneDLog_sound : B3_1_4U2_0_2EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 3 1 4) (shape 2 0 2) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B3_1_4U2_0_2OneD_sound) (w := B3_1_4U2_0_2EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma B3_1_4U2_0_2EOneD_sound : B3_1_4U2_0_2EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 3 1 4) (shape 2 0 2) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B3_1_4U2_0_2OneD_sound) B3_1_4U2_0_2EOneDLog_sound) (by decide +kernel)
lemma B3_1_4U2_0_2BinaryEntropy_sound : B3_1_4U2_0_2BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 3 1 4) (shape 2 0 2))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B3_1_4U2_0_2EOneD_sound B3_1_4U2_0_2ED_sound)
    (Ball.mul_sound B3_1_4U2_0_2D_sound logN2_sound)) (by decide +kernel)
lemma B3_1_4U2_0_2Leaf_sound : B3_1_4U2_0_2Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 1 4) (shape 2 0 2)) := by
  have hh : shapeMax (shape 2 0 2) = 2 := by decide +kernel
  have hp : positive (shape 2 0 2) = false := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_false,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, if_false, ite_true, if_true]
  exact contains_sound (Ball.add_sound B3_1_4U2_0_2BinaryEntropy_sound
    (Ball.mul_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      B3_1_4U2_0_2OneD_sound) logN5_sound)) (by decide +kernel)
lemma B3_1_4U2_1_1Leaf_sound : B3_1_4U2_1_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 1 4) (shape 2 1 1)) := by
  have hh : shapeMax (shape 2 1 1) = 2 := by decide +kernel
  have hp : positive (shape 2 1 1) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, if_false]
  have ht : (Ball.exact (978917 / 500000)).Encloses (2 - (binaryParameter (shape 3 1 4) (shape 2 1 1) : ℝ)) := by
    have he : binaryParameter (shape 3 1 4) (shape 2 1 1) = (21083 / 500000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((978917 / 500000) : ℚ) using 1
    all_goals try with_reducible_and_instances rfl
    norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
lemma B3_1_4U3_0_1Leaf_sound : B3_1_4U3_0_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 1 4) (shape 3 0 1)) := by
  have hh : shapeMax (shape 3 0 1) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, if_false, ite_true, if_true]
  exact logN10_sound
lemma B3_1_4U3_1_0Leaf_sound : B3_1_4U3_1_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 1 4) (shape 3 1 0)) := by
  have hh : shapeMax (shape 3 1 0) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, if_false, ite_true, if_true]
  exact logN10_sound
lemma B3_1_4Leaves_sound (u : Shape) (hu : u ∈ below (shape 3 1 4)) :
    (B3_1_4Leaves u).Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 1 4) u) := by
  rw [B3_1_4_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B3_1_4U0_0_4Leaf_sound
  · exact B3_1_4U0_1_3Leaf_sound
  · exact B3_1_4U1_0_3Leaf_sound
  · exact B3_1_4U1_1_2Leaf_sound
  · exact B3_1_4U2_0_2Leaf_sound
  · exact B3_1_4U2_1_1Leaf_sound
  · exact B3_1_4U3_0_1Leaf_sound
  · exact B3_1_4U3_1_0Leaf_sound
lemma B3_1_4S2_sound_oai : B3_1_4S2.Encloses
    (((below (shape 3 1 4)).map fun u => (littleMass (shape 3 1 4) u : ℝ) * AllFieldTerminalRates.secondLeafRate (shape 3 1 4) u).sum) := by
  exact contains_sound (listSumBall_sound (below (shape 3 1 4))
    (fun u => .mul (B3_1_4Masses u) (B3_1_4Leaves u)) _
    (fun u hu => Ball.mul_sound (B3_1_4Masses_sound u hu) (B3_1_4Leaves_sound u hu))) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_1_4S2_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_1_4S2_sound_oai
