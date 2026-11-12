-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_4_3S2_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T07:12:36.60961+00:00
-- url     : https://prove2.me/submissions/6280b9ea-645d-4cb0-a903-0d4aa902a368

import Mathlib
import Definitions.Def_OAIQ254M002
import Definitions.Def_OAIQ254M003
import Definitions.Def_OAIQ254M005
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_mul_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkLog_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B1_4_3Masses_sound
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

lemma B1_4_3_below : below (shape 1 4 3) = [
  (shape 0 1 3),
  (shape 0 2 2),
  (shape 0 3 1),
  (shape 0 4 0),
  (shape 1 0 3),
  (shape 1 1 2),
  (shape 1 2 1),
  (shape 1 3 0)] := by decide +kernel

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal1_4_3
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
lemma B1_4_3U0_1_3Leaf_sound : B1_4_3U0_1_3Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 4 3) (shape 0 1 3)) := by
  have hh : shapeMax (shape 0 1 3) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, if_false, ite_true, if_true]
  exact logN10_sound
lemma B1_4_3U0_2_2D_sound : B1_4_3U0_2_2D.Encloses (binaryParameter (shape 1 4 3) (shape 0 2 2) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
lemma B1_4_3U0_2_2OneD_sound : B1_4_3U0_2_2OneD.Encloses (1 - (binaryParameter (shape 1 4 3) (shape 0 2 2) : ℝ)) := by
  have he : binaryParameter (shape 1 4 3) (shape 0 2 2) = (23901 / 250000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((226099 / 250000) : ℚ) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [B1_4_3U0_2_2OneD, Ball.exact])
lemma B1_4_3U0_2_2EDLog_sound : B1_4_3U0_2_2EDLog.Encloses (Real.log ((binaryParameter (shape 1 4 3) (shape 0 2 2) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B1_4_3U0_2_2D_sound) (w := B1_4_3U0_2_2EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma B1_4_3U0_2_2ED_sound : B1_4_3U0_2_2ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 1 4 3) (shape 0 2 2) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B1_4_3U0_2_2D_sound) B1_4_3U0_2_2EDLog_sound) (by decide +kernel)
lemma B1_4_3U0_2_2EOneDLog_sound : B1_4_3U0_2_2EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 1 4 3) (shape 0 2 2) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B1_4_3U0_2_2OneD_sound) (w := B1_4_3U0_2_2EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma B1_4_3U0_2_2EOneD_sound : B1_4_3U0_2_2EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 1 4 3) (shape 0 2 2) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B1_4_3U0_2_2OneD_sound) B1_4_3U0_2_2EOneDLog_sound) (by decide +kernel)
lemma B1_4_3U0_2_2BinaryEntropy_sound : B1_4_3U0_2_2BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 1 4 3) (shape 0 2 2))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B1_4_3U0_2_2EOneD_sound B1_4_3U0_2_2ED_sound)
    (Ball.mul_sound B1_4_3U0_2_2D_sound logN2_sound)) (by decide +kernel)
lemma B1_4_3U0_2_2Leaf_sound : B1_4_3U0_2_2Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 4 3) (shape 0 2 2)) := by
  have hh : shapeMax (shape 0 2 2) = 2 := by decide +kernel
  have hp : positive (shape 0 2 2) = false := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_false,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, if_false, ite_true, if_true]
  exact contains_sound (Ball.add_sound B1_4_3U0_2_2BinaryEntropy_sound
    (Ball.mul_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      B1_4_3U0_2_2OneD_sound) logN5_sound)) (by decide +kernel)
lemma B1_4_3U0_3_1Leaf_sound : B1_4_3U0_3_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 4 3) (shape 0 3 1)) := by
  have hh : shapeMax (shape 0 3 1) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, if_false, ite_true, if_true]
  exact logN10_sound
lemma B1_4_3U0_4_0Leaf_sound : B1_4_3U0_4_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 4 3) (shape 0 4 0)) := by
  have hh : shapeMax (shape 0 4 0) = 4 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, ite_true, if_true]
  simpa only [B1_4_3U0_4_0Leaf, Ball.exact, Rat.cast_zero] using Ball.exact_sound 0
lemma B1_4_3U1_0_3Leaf_sound : B1_4_3U1_0_3Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 4 3) (shape 1 0 3)) := by
  have hh : shapeMax (shape 1 0 3) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, if_false, ite_true, if_true]
  exact logN10_sound
lemma B1_4_3U1_1_2Leaf_sound : B1_4_3U1_1_2Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 4 3) (shape 1 1 2)) := by
  have hh : shapeMax (shape 1 1 2) = 2 := by decide +kernel
  have hp : positive (shape 1 1 2) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, if_false]
  have ht : (Ball.exact (1958257 / 1000000)).Encloses (2 - (binaryParameter (shape 1 4 3) (shape 1 1 2) : ℝ)) := by
    have he : binaryParameter (shape 1 4 3) (shape 1 1 2) = (41743 / 1000000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((1958257 / 1000000) : ℚ) using 1
    all_goals try with_reducible_and_instances rfl
    norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
lemma B1_4_3U1_2_1Leaf_sound : B1_4_3U1_2_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 4 3) (shape 1 2 1)) := by
  have hh : shapeMax (shape 1 2 1) = 2 := by decide +kernel
  have hp : positive (shape 1 2 1) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, if_false]
  have ht : (Ball.exact (1996943 / 1000000)).Encloses (2 - (binaryParameter (shape 1 4 3) (shape 1 2 1) : ℝ)) := by
    have he : binaryParameter (shape 1 4 3) (shape 1 2 1) = (3057 / 1000000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((1996943 / 1000000) : ℚ) using 1
    all_goals try with_reducible_and_instances rfl
    norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
lemma B1_4_3U1_3_0Leaf_sound : B1_4_3U1_3_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 4 3) (shape 1 3 0)) := by
  have hh : shapeMax (shape 1 3 0) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, if_false, ite_true, if_true]
  exact logN10_sound
lemma B1_4_3Leaves_sound (u : Shape) (hu : u ∈ below (shape 1 4 3)) :
    (B1_4_3Leaves u).Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 4 3) u) := by
  rw [B1_4_3_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B1_4_3U0_1_3Leaf_sound
  · exact B1_4_3U0_2_2Leaf_sound
  · exact B1_4_3U0_3_1Leaf_sound
  · exact B1_4_3U0_4_0Leaf_sound
  · exact B1_4_3U1_0_3Leaf_sound
  · exact B1_4_3U1_1_2Leaf_sound
  · exact B1_4_3U1_2_1Leaf_sound
  · exact B1_4_3U1_3_0Leaf_sound
lemma B1_4_3S2_sound_oai : B1_4_3S2.Encloses
    (((below (shape 1 4 3)).map fun u => (littleMass (shape 1 4 3) u : ℝ) * AllFieldTerminalRates.secondLeafRate (shape 1 4 3) u).sum) := by
  exact contains_sound (listSumBall_sound (below (shape 1 4 3))
    (fun u => .mul (B1_4_3Masses u) (B1_4_3Leaves u)) _
    (fun u hu => Ball.mul_sound (B1_4_3Masses_sound u hu) (B1_4_3Leaves_sound u hu))) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_4_3S2_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_4_3S2_sound_oai
