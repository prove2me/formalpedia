-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2S2_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T06:09:15.292257+00:00
-- url     : https://prove2.me/submissions/9d67c37f-d636-4c3e-a031-add61518bfa8

import Mathlib
import Definitions.Def_OAIQ254M002
import Definitions.Def_OAIQ254M003
import Definitions.Def_OAIQ254M005
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkLog_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_normalizedLogBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B3_3_2Masses_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B3_3_2U0_2_2ED_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B3_3_2U0_2_2EOneD_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B3_3_2U1_1_2Leaf_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B3_3_2U1_2_1Leaf_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B3_3_2U2_0_2ED_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B3_3_2U2_0_2EOneD_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B3_3_2U2_1_1Leaf_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B3_3_2U2_2_0ED_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B3_3_2U2_2_0EOneD_sound

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_CertificatesReplay
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons
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

theorem nonnegative_radius {b : Ball} {x : ℝ} (h : b.Encloses x) : 0 ≤ b.radius := by
  have : (0 : ℝ) ≤ b.radius := (abs_nonneg _).trans h
  exact_mod_cast this

theorem exact_sound (q : ℚ) : (exact q).Encloses (q : ℝ) := by
  simp [Encloses, exact]

theorem add_sound {a b : Ball} {x y : ℝ} (hx : a.Encloses x) (hy : b.Encloses y) :
    (add a b).Encloses (x + y) := by
  unfold Encloses add
  simp only [Rat.cast_add]
  calc
    _ = |(x - (a.center : ℝ)) + (y - (b.center : ℝ))| := by congr 1; ring
    _ ≤ |x - (a.center : ℝ)| + |y - (b.center : ℝ)| := abs_add_le _ _
    _ ≤ _ := add_le_add hx hy

theorem mul_sound {a b : Ball} {x y : ℝ} (hx : a.Encloses x) (hy : b.Encloses y) :
    (mul a b).Encloses (x * y) := by
  have ha : (0 : ℝ) ≤ a.radius := by exact_mod_cast nonnegative_radius hx
  have hb : (0 : ℝ) ≤ b.radius := by exact_mod_cast nonnegative_radius hy
  unfold Encloses mul
  simp only [Rat.cast_mul, Rat.cast_add, Rat.cast_abs]
  calc
    _ = |(a.center : ℝ) * (y - (b.center : ℝ)) +
          (b.center : ℝ) * (x - (a.center : ℝ)) +
          (x - (a.center : ℝ)) * (y - (b.center : ℝ))| := by congr 1; ring
    _ ≤ |(a.center : ℝ) * (y - (b.center : ℝ))| +
          |(b.center : ℝ) * (x - (a.center : ℝ))| +
          |(x - (a.center : ℝ)) * (y - (b.center : ℝ))| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))
    _ = |(a.center : ℝ)| * |y - (b.center : ℝ)| +
          |(b.center : ℝ)| * |x - (a.center : ℝ)| +
          |x - (a.center : ℝ)| * |y - (b.center : ℝ)| := by simp only [abs_mul]
    _ ≤ _ := add_le_add
      (add_le_add (mul_le_mul_of_nonneg_left hy (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hx (abs_nonneg _)))
      (mul_le_mul hx hy (abs_nonneg _) ha)

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

lemma logTwoBall_sound : logTwoBall.Encloses (Real.log 2) := by
  have h := normalizedLogBall_sound (m := 2) (trace := logTwoTrace)
    (by norm_num) (by norm_num) (by decide +kernel)
  exact contains_sound h (by decide +kernel)

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
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal3_3_2
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
open AllFieldInitialEntropyCertificate
open scoped BigOperators
lemma B3_3_2_below : below (shape 3 3 2) = [
  (shape 0 2 2),
  (shape 0 3 1),
  (shape 1 1 2),
  (shape 1 2 1),
  (shape 1 3 0),
  (shape 2 0 2),
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
lemma B3_3_2U0_2_2D_sound : B3_3_2U0_2_2D.Encloses (binaryParameter (shape 3 3 2) (shape 0 2 2) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
lemma B3_3_2U0_2_2OneD_sound : B3_3_2U0_2_2OneD.Encloses (1 - (binaryParameter (shape 3 3 2) (shape 0 2 2) : ℝ)) := by
  have he : binaryParameter (shape 3 3 2) (shape 0 2 2) = (52157 / 500000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((447843 / 500000) : ℚ) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [B3_3_2U0_2_2OneD, Ball.exact])
lemma B3_3_2U0_2_2BinaryEntropy_sound : B3_3_2U0_2_2BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 3 3 2) (shape 0 2 2))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B3_3_2U0_2_2EOneD_sound B3_3_2U0_2_2ED_sound)
    (Ball.mul_sound B3_3_2U0_2_2D_sound logN2_sound)) (by decide +kernel)
lemma B3_3_2U0_2_2Leaf_sound : B3_3_2U0_2_2Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 3 2) (shape 0 2 2)) := by
  have hh : shapeMax (shape 0 2 2) = 2 := by decide +kernel
  have hp : positive (shape 0 2 2) = false := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_false,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, if_false, ite_true, if_true]
  exact contains_sound (Ball.add_sound B3_3_2U0_2_2BinaryEntropy_sound
    (Ball.mul_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      B3_3_2U0_2_2OneD_sound) logN5_sound)) (by decide +kernel)
lemma B3_3_2U0_3_1Leaf_sound : B3_3_2U0_3_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 3 2) (shape 0 3 1)) := by
  have hh : shapeMax (shape 0 3 1) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, if_false, ite_true, if_true]
  exact logN10_sound
lemma B3_3_2U1_3_0Leaf_sound : B3_3_2U1_3_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 3 2) (shape 1 3 0)) := by
  have hh : shapeMax (shape 1 3 0) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, if_false, ite_true, if_true]
  exact logN10_sound
lemma B3_3_2U2_0_2D_sound : B3_3_2U2_0_2D.Encloses (binaryParameter (shape 3 3 2) (shape 2 0 2) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
lemma B3_3_2U2_0_2OneD_sound : B3_3_2U2_0_2OneD.Encloses (1 - (binaryParameter (shape 3 3 2) (shape 2 0 2) : ℝ)) := by
  have he : binaryParameter (shape 3 3 2) (shape 2 0 2) = (20479 / 200000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((179521 / 200000) : ℚ) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [B3_3_2U2_0_2OneD, Ball.exact])
lemma B3_3_2U2_0_2BinaryEntropy_sound : B3_3_2U2_0_2BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 3 3 2) (shape 2 0 2))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B3_3_2U2_0_2EOneD_sound B3_3_2U2_0_2ED_sound)
    (Ball.mul_sound B3_3_2U2_0_2D_sound logN2_sound)) (by decide +kernel)
lemma B3_3_2U2_0_2Leaf_sound : B3_3_2U2_0_2Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 3 2) (shape 2 0 2)) := by
  have hh : shapeMax (shape 2 0 2) = 2 := by decide +kernel
  have hp : positive (shape 2 0 2) = false := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_false,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, if_false, ite_true, if_true]
  exact contains_sound (Ball.add_sound B3_3_2U2_0_2BinaryEntropy_sound
    (Ball.mul_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      B3_3_2U2_0_2OneD_sound) logN5_sound)) (by decide +kernel)
lemma B3_3_2U2_2_0D_sound : B3_3_2U2_2_0D.Encloses (binaryParameter (shape 3 3 2) (shape 2 2 0) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
lemma B3_3_2U2_2_0OneD_sound : B3_3_2U2_2_0OneD.Encloses (1 - (binaryParameter (shape 3 3 2) (shape 2 2 0) : ℝ)) := by
  have he : binaryParameter (shape 3 3 2) (shape 2 2 0) = (27517 / 250000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((222483 / 250000) : ℚ) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [B3_3_2U2_2_0OneD, Ball.exact])
lemma B3_3_2U2_2_0BinaryEntropy_sound : B3_3_2U2_2_0BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 3 3 2) (shape 2 2 0))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B3_3_2U2_2_0EOneD_sound B3_3_2U2_2_0ED_sound)
    (Ball.mul_sound B3_3_2U2_2_0D_sound logN2_sound)) (by decide +kernel)
lemma B3_3_2U2_2_0Leaf_sound : B3_3_2U2_2_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 3 2) (shape 2 2 0)) := by
  have hh : shapeMax (shape 2 2 0) = 2 := by decide +kernel
  have hp : positive (shape 2 2 0) = false := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_false,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, if_false, ite_true, if_true]
  exact contains_sound (Ball.add_sound B3_3_2U2_2_0BinaryEntropy_sound
    (Ball.mul_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      B3_3_2U2_2_0OneD_sound) logN5_sound)) (by decide +kernel)
lemma B3_3_2U3_0_1Leaf_sound : B3_3_2U3_0_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 3 2) (shape 3 0 1)) := by
  have hh : shapeMax (shape 3 0 1) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, if_false, ite_true, if_true]
  exact logN10_sound
lemma B3_3_2U3_1_0Leaf_sound : B3_3_2U3_1_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 3 2) (shape 3 1 0)) := by
  have hh : shapeMax (shape 3 1 0) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, if_false, ite_true, if_true]
  exact logN10_sound
lemma B3_3_2Leaves_sound (u : Shape) (hu : u ∈ below (shape 3 3 2)) :
    (B3_3_2Leaves u).Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 3 2) u) := by
  rw [B3_3_2_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B3_3_2U0_2_2Leaf_sound
  · exact B3_3_2U0_3_1Leaf_sound
  · exact B3_3_2U1_1_2Leaf_sound
  · exact B3_3_2U1_2_1Leaf_sound
  · exact B3_3_2U1_3_0Leaf_sound
  · exact B3_3_2U2_0_2Leaf_sound
  · exact B3_3_2U2_1_1Leaf_sound
  · exact B3_3_2U2_2_0Leaf_sound
  · exact B3_3_2U3_0_1Leaf_sound
  · exact B3_3_2U3_1_0Leaf_sound
lemma B3_3_2S2_sound_oai : B3_3_2S2.Encloses
    (((below (shape 3 3 2)).map fun u => (littleMass (shape 3 3 2) u : ℝ) * AllFieldTerminalRates.secondLeafRate (shape 3 3 2) u).sum) := by
  exact contains_sound (listSumBall_sound (below (shape 3 3 2))
    (fun u => .mul (B3_3_2Masses u) (B3_3_2Leaves u)) _
    (fun u hu => Ball.mul_sound (B3_3_2Masses_sound u hu) (B3_3_2Leaves_sound u hu))) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2S2_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2S2_sound_oai
