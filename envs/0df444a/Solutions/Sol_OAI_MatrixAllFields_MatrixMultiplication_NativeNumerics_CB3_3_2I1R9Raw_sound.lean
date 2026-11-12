-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I1R9Raw_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T14:28:33.03811+00:00
-- url     : https://prove2.me/submissions/b1ae6020-55e3-41cf-be21-ca4aaf85a6cf

import Mathlib
import Definitions.Def_OAIQ254M010
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_inv_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_mul_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B3_3_2Den_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B3_3_2Raw_sound

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

lemma residualBall_sound_on {A : Type*} [Fintype A] (support : List Shape)
    (bs : Shape → Ball) (p : Shape → ℝ) (priority : Placement) (position : Fin 3)
    (bq : Shape → A → Ball) (q : Shape → A → ℝ)
    (hp : ∀ u ∈ support, (bs u).Encloses (p u))
    (hq : ∀ u ∈ support, ∀ a, (bq u a).Encloses (q u a)) (k : Fin 17) (a : A) :
    (residualBall support bs priority position bq k a).Encloses
      (residualLaw support p priority position q k a) := by
  apply listSumBall_sound
  intro u hu
  by_cases hk : ¬ designated priority position u ∧ u (priority position) = k.val
  · simpa only [ite_eq_left hk] using Ball.mul_sound (hp u hu) (hq u hu a)
  · simpa only [hk, ite_false, if_false, Rat.cast_zero] using Ball.exact_sound 0

end MatrixMultiplication.NativeNumerics

end
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
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal3_3_2
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
lemma B3_3_2Den_positive : 0 < B3_3_2Den.lower := by decide +kernel
lemma B3_3_2Law_check_0_2_2 : contains (.mul (B3_3_2Raw (shape 0 2 2)) (.inv B3_3_2Den)) (B3_3_2Table (shape 0 2 2)) = true := by decide +kernel
lemma B3_3_2Law_check_0_3_1 : contains (.mul (B3_3_2Raw (shape 0 3 1)) (.inv B3_3_2Den)) (B3_3_2Table (shape 0 3 1)) = true := by decide +kernel
lemma B3_3_2Law_check_1_1_2 : contains (.mul (B3_3_2Raw (shape 1 1 2)) (.inv B3_3_2Den)) (B3_3_2Table (shape 1 1 2)) = true := by decide +kernel
lemma B3_3_2Law_check_1_2_1 : contains (.mul (B3_3_2Raw (shape 1 2 1)) (.inv B3_3_2Den)) (B3_3_2Table (shape 1 2 1)) = true := by decide +kernel
lemma B3_3_2Law_check_1_3_0 : contains (.mul (B3_3_2Raw (shape 1 3 0)) (.inv B3_3_2Den)) (B3_3_2Table (shape 1 3 0)) = true := by decide +kernel
lemma B3_3_2Law_check_2_0_2 : contains (.mul (B3_3_2Raw (shape 2 0 2)) (.inv B3_3_2Den)) (B3_3_2Table (shape 2 0 2)) = true := by decide +kernel
lemma B3_3_2Law_check_2_1_1 : contains (.mul (B3_3_2Raw (shape 2 1 1)) (.inv B3_3_2Den)) (B3_3_2Table (shape 2 1 1)) = true := by decide +kernel
lemma B3_3_2Law_check_2_2_0 : contains (.mul (B3_3_2Raw (shape 2 2 0)) (.inv B3_3_2Den)) (B3_3_2Table (shape 2 2 0)) = true := by decide +kernel
lemma B3_3_2Law_check_3_0_1 : contains (.mul (B3_3_2Raw (shape 3 0 1)) (.inv B3_3_2Den)) (B3_3_2Table (shape 3 0 1)) = true := by decide +kernel
lemma B3_3_2Law_check_3_1_0 : contains (.mul (B3_3_2Raw (shape 3 1 0)) (.inv B3_3_2Den)) (B3_3_2Table (shape 3 1 0)) = true := by decide +kernel
lemma B3_3_2Law_check (u : Shape) (hu : u ∈ below (shape 3 3 2)) :
    contains (.mul (B3_3_2Raw u) (.inv B3_3_2Den)) (B3_3_2Table u) = true := by
  rw [B3_3_2_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B3_3_2Law_check_0_2_2
  · exact B3_3_2Law_check_0_3_1
  · exact B3_3_2Law_check_1_1_2
  · exact B3_3_2Law_check_1_2_1
  · exact B3_3_2Law_check_1_3_0
  · exact B3_3_2Law_check_2_0_2
  · exact B3_3_2Law_check_2_1_1
  · exact B3_3_2Law_check_2_2_0
  · exact B3_3_2Law_check_3_0_1
  · exact B3_3_2Law_check_3_1_0
lemma B3_3_2Law_sound (u : Shape) :
    (B3_3_2Law u).Encloses (stageBLaw (shape 3 3 2) u : ℝ) := by
  by_cases hu : u ∈ below (shape 3 3 2)
  · have h := contains_sound (Ball.mul_sound (B3_3_2Raw_sound u hu)
      (Ball.inv_sound B3_3_2Den_sound B3_3_2Den_positive)) (B3_3_2Law_check u hu)
    simpa only [B3_3_2Law, hu, ite_true, if_true, stageBLaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [B3_3_2Law, hu, ite_false, if_false, stageBLaw, splitLaw, Rat.cast_zero]
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
lemma B3_3_2Binary_eq (u : Shape) (hu : u ∈ shapes 4) :
    binaryParameter (shape 3 3 2) u = B3_3_2Binary u := by
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

lemma B3_3_2Little_sound (u : Shape) (w : Fin 3) (i : Fin 6) :
    (B3_3_2Little u w i).Encloses (littleLaw (shape 3 3 2) u w i : ℝ) := by
  by_cases hu : u ∈ shapes 4
  · simp only [B3_3_2Little, hu, ite_true, if_true]
    apply exact_rat_enclosed
    simp only [B3_3_2LittleRat, littleLaw, B3_3_2Binary_eq u hu]
  · simp only [B3_3_2Little, hu, ite_false, if_false]
    exact Ball.exact_sound _

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB3_3_2I1
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
lemma CB3_3_2I1R9Raw_sound_oai (a : Fin 6) :
    (CB3_3_2I1R9Raw a).Encloses (CB3_3_2I1R9Value a) := by
  exact residualBall_sound_on (below (shape 3 3 2)) B3_3_2Law (fun u => (stageBLaw (shape 3 3 2) u : ℝ)) (stageBPriority (shape 3 3 2)) 1 (fun u => B3_3_2Little u ((stageBPriority (shape 3 3 2)) 1)) (fun u a => (littleLaw (shape 3 3 2) u ((stageBPriority (shape 3 3 2)) 1) a : ℝ)) (fun u _ => B3_3_2Law_sound u) (fun u _ a => B3_3_2Little_sound u ((stageBPriority (shape 3 3 2)) 1) a) 9 a

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I1R9Raw_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I1R9Raw_sound_oai
