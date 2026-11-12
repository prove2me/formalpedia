-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z0_7_1Half_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:58:33.0495+00:00
-- url     : https://prove2.me/submissions/3d94f4b7-0cae-412e-9082-a4ec105092cd

import Mathlib
import Definitions.Def_OAIQ254M007
import Definitions.Def_OAIQ254M011
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_inv_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_mul_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound

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
open AllFieldInitialEntropyCertificate
open scoped BigOperators

lemma list_cast_enclosed {A : Type*} (xs : List A) (b : A → Ball) (v : A → ℚ)
    (h : ∀ a ∈ xs, (b a).Encloses (v a : ℝ)) :
    (listSumBall xs b).Encloses ((xs.map v).sum : ℝ) := by
  simpa only [Rat.cast_list_sum, List.map_map, Function.comp_def] using
    listSumBall_sound xs b (fun a => (v a : ℝ)) h

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

lemma forall_fin6 {P : Fin 6 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2)
    (h3 : P 3) (h4 : P 4) (h5 : P 5) : ∀ i, P i := by
  intro i
  fin_cases i <;> assumption

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Zero0_1_7
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
lemma w195_sound : w195.Encloses (weight 0 : ℝ) := by
  have he : weight 0 = 1 := by decide +kernel
  rw [he, Rat.cast_one]
  simpa only [w195, Rat.cast_one] using Ball.exact_sound 1

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Four0_7_1
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
lemma Z0_7_1Raw_sound_0 (j : Fin 6) :
    (Z0_7_1Raw (0,j)).Encloses (weight (orderedPairInteger (shape 0 7 1) 0 j) : ℝ) := by
  fin_cases j
  · change (Z0_7_1Raw (0,0)).Encloses (weight (orderedPairInteger (shape 0 7 1) 0 0) : ℝ)
    have he : orderedPairInteger (shape 0 7 1) 0 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_7_1Raw (0,1)).Encloses (weight (orderedPairInteger (shape 0 7 1) 0 1) : ℝ)
    have he : orderedPairInteger (shape 0 7 1) 0 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_7_1Raw (0,2)).Encloses (weight (orderedPairInteger (shape 0 7 1) 0 2) : ℝ)
    have he : orderedPairInteger (shape 0 7 1) 0 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_7_1Raw (0,3)).Encloses (weight (orderedPairInteger (shape 0 7 1) 0 3) : ℝ)
    have he : orderedPairInteger (shape 0 7 1) 0 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_7_1Raw (0,4)).Encloses (weight (orderedPairInteger (shape 0 7 1) 0 4) : ℝ)
    have he : orderedPairInteger (shape 0 7 1) 0 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_7_1Raw (0,5)).Encloses (weight (orderedPairInteger (shape 0 7 1) 0 5) : ℝ)
    have he : orderedPairInteger (shape 0 7 1) 0 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_7_1Raw_sound_1 (j : Fin 6) :
    (Z0_7_1Raw (1,j)).Encloses (weight (orderedPairInteger (shape 0 7 1) 1 j) : ℝ) := by
  fin_cases j
  · change (Z0_7_1Raw (1,0)).Encloses (weight (orderedPairInteger (shape 0 7 1) 1 0) : ℝ)
    have he : orderedPairInteger (shape 0 7 1) 1 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_7_1Raw (1,1)).Encloses (weight (orderedPairInteger (shape 0 7 1) 1 1) : ℝ)
    have he : orderedPairInteger (shape 0 7 1) 1 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_7_1Raw (1,2)).Encloses (weight (orderedPairInteger (shape 0 7 1) 1 2) : ℝ)
    have he : orderedPairInteger (shape 0 7 1) 1 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_7_1Raw (1,3)).Encloses (weight (orderedPairInteger (shape 0 7 1) 1 3) : ℝ)
    have he : orderedPairInteger (shape 0 7 1) 1 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_7_1Raw (1,4)).Encloses (weight (orderedPairInteger (shape 0 7 1) 1 4) : ℝ)
    have he : orderedPairInteger (shape 0 7 1) 1 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_7_1Raw (1,5)).Encloses (weight (orderedPairInteger (shape 0 7 1) 1 5) : ℝ)
    have he : orderedPairInteger (shape 0 7 1) 1 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_7_1Raw_sound_2 (j : Fin 6) :
    (Z0_7_1Raw (2,j)).Encloses (weight (orderedPairInteger (shape 0 7 1) 2 j) : ℝ) := by
  fin_cases j
  · change (Z0_7_1Raw (2,0)).Encloses (weight (orderedPairInteger (shape 0 7 1) 2 0) : ℝ)
    have he : orderedPairInteger (shape 0 7 1) 2 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_7_1Raw (2,1)).Encloses (weight (orderedPairInteger (shape 0 7 1) 2 1) : ℝ)
    have he : orderedPairInteger (shape 0 7 1) 2 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_7_1Raw (2,2)).Encloses (weight (orderedPairInteger (shape 0 7 1) 2 2) : ℝ)
    have he : orderedPairInteger (shape 0 7 1) 2 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_7_1Raw (2,3)).Encloses (weight (orderedPairInteger (shape 0 7 1) 2 3) : ℝ)
    have he : orderedPairInteger (shape 0 7 1) 2 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_7_1Raw (2,4)).Encloses (weight (orderedPairInteger (shape 0 7 1) 2 4) : ℝ)
    have he : orderedPairInteger (shape 0 7 1) 2 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_7_1Raw (2,5)).Encloses (weight (orderedPairInteger (shape 0 7 1) 2 5) : ℝ)
    have he : orderedPairInteger (shape 0 7 1) 2 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_7_1Raw_sound_3 (j : Fin 6) :
    (Z0_7_1Raw (3,j)).Encloses (weight (orderedPairInteger (shape 0 7 1) 3 j) : ℝ) := by
  fin_cases j
  · change (Z0_7_1Raw (3,0)).Encloses (weight (orderedPairInteger (shape 0 7 1) 3 0) : ℝ)
    have he : orderedPairInteger (shape 0 7 1) 3 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_7_1Raw (3,1)).Encloses (weight (orderedPairInteger (shape 0 7 1) 3 1) : ℝ)
    have he : orderedPairInteger (shape 0 7 1) 3 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_7_1Raw (3,2)).Encloses (weight (orderedPairInteger (shape 0 7 1) 3 2) : ℝ)
    have he : orderedPairInteger (shape 0 7 1) 3 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_7_1Raw (3,3)).Encloses (weight (orderedPairInteger (shape 0 7 1) 3 3) : ℝ)
    have he : orderedPairInteger (shape 0 7 1) 3 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_7_1Raw (3,4)).Encloses (weight (orderedPairInteger (shape 0 7 1) 3 4) : ℝ)
    have he : orderedPairInteger (shape 0 7 1) 3 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_7_1Raw (3,5)).Encloses (weight (orderedPairInteger (shape 0 7 1) 3 5) : ℝ)
    have he : orderedPairInteger (shape 0 7 1) 3 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_7_1Raw_sound_4 (j : Fin 6) :
    (Z0_7_1Raw (4,j)).Encloses (weight (orderedPairInteger (shape 0 7 1) 4 j) : ℝ) := by
  fin_cases j
  · change (Z0_7_1Raw (4,0)).Encloses (weight (orderedPairInteger (shape 0 7 1) 4 0) : ℝ)
    have he : orderedPairInteger (shape 0 7 1) 4 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_7_1Raw (4,1)).Encloses (weight (orderedPairInteger (shape 0 7 1) 4 1) : ℝ)
    have he : orderedPairInteger (shape 0 7 1) 4 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_7_1Raw (4,2)).Encloses (weight (orderedPairInteger (shape 0 7 1) 4 2) : ℝ)
    have he : orderedPairInteger (shape 0 7 1) 4 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_7_1Raw (4,3)).Encloses (weight (orderedPairInteger (shape 0 7 1) 4 3) : ℝ)
    have he : orderedPairInteger (shape 0 7 1) 4 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_7_1Raw (4,4)).Encloses (weight (orderedPairInteger (shape 0 7 1) 4 4) : ℝ)
    have he : orderedPairInteger (shape 0 7 1) 4 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_7_1Raw (4,5)).Encloses (weight (orderedPairInteger (shape 0 7 1) 4 5) : ℝ)
    have he : orderedPairInteger (shape 0 7 1) 4 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_7_1Raw_sound_5 (j : Fin 6) :
    (Z0_7_1Raw (5,j)).Encloses (weight (orderedPairInteger (shape 0 7 1) 5 j) : ℝ) := by
  fin_cases j
  · change (Z0_7_1Raw (5,0)).Encloses (weight (orderedPairInteger (shape 0 7 1) 5 0) : ℝ)
    have he : orderedPairInteger (shape 0 7 1) 5 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_7_1Raw (5,1)).Encloses (weight (orderedPairInteger (shape 0 7 1) 5 1) : ℝ)
    have he : orderedPairInteger (shape 0 7 1) 5 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_7_1Raw (5,2)).Encloses (weight (orderedPairInteger (shape 0 7 1) 5 2) : ℝ)
    have he : orderedPairInteger (shape 0 7 1) 5 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_7_1Raw (5,3)).Encloses (weight (orderedPairInteger (shape 0 7 1) 5 3) : ℝ)
    have he : orderedPairInteger (shape 0 7 1) 5 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_7_1Raw (5,4)).Encloses (weight (orderedPairInteger (shape 0 7 1) 5 4) : ℝ)
    have he : orderedPairInteger (shape 0 7 1) 5 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_7_1Raw (5,5)).Encloses (weight (orderedPairInteger (shape 0 7 1) 5 5) : ℝ)
    have he : orderedPairInteger (shape 0 7 1) 5 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_7_1Raw_sound (ij : PairSlot) :
    (Z0_7_1Raw ij).Encloses (weight (orderedPairInteger (shape 0 7 1) ij.1 ij.2) : ℝ) := by
  rcases ij with ⟨i,j⟩
  revert i
  exact forall_fin6 (Z0_7_1Raw_sound_0 j) (Z0_7_1Raw_sound_1 j) (Z0_7_1Raw_sound_2 j) (Z0_7_1Raw_sound_3 j) (Z0_7_1Raw_sound_4 j) (Z0_7_1Raw_sound_5 j)
lemma Z0_7_1Den_sound : Z0_7_1Den.Encloses
    (((orderedPairs (shape 0 7 1)).map (fun ij => weight (orderedPairInteger (shape 0 7 1) ij.1 ij.2))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (orderedPairs (shape 0 7 1)) Z0_7_1Raw
    (fun ij => weight (orderedPairInteger (shape 0 7 1) ij.1 ij.2))
    (fun ij _ => Z0_7_1Raw_sound ij)) (by decide +kernel)
lemma Z0_7_1Den_pos : 0 < Z0_7_1Den.lower := by decide +kernel
lemma Z0_7_1Contains : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j = shapeMax (shape 0 7 1) →
    contains (.mul (Z0_7_1Raw (i,j)) (.inv Z0_7_1Den)) (Z0_7_1Probs (i,j)) = true := by
  decide +kernel
lemma Z0_7_1Zero : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j ≠ shapeMax (shape 0 7 1) → Z0_7_1Probs (i,j) = .exact 0 := by
  decide +kernel
lemma Z0_7_1Probs_sound (ij : PairSlot) :
    (Z0_7_1Probs ij).Encloses (zeroPairLaw (shape 0 7 1) ij.1 ij.2 : ℝ) := by
  by_cases h : statisticWeight ij.1 + statisticWeight ij.2 = shapeMax (shape 0 7 1)
  · have hb := contains_sound (Ball.mul_sound (Z0_7_1Raw_sound ij)
      (Ball.inv_sound Z0_7_1Den_sound Z0_7_1Den_pos)) (Z0_7_1Contains ij.1 ij.2 h)
    simpa only [zeroPairLaw, h, ite_true, if_true, Rat.cast_div, Rat.cast_mul,
      Rat.cast_inv, div_eq_mul_inv] using hb
  · rw [Z0_7_1Zero ij.1 ij.2 h]
    simpa only [zeroPairLaw, h, ite_false, if_false] using Ball.exact_sound 0

lemma Z0_7_1Half_sound_oai (w : Fin 3) (ij : PairSlot) :
    (Z0_7_1Half w ij).Encloses (halfLaw (shape 0 7 1) w ij : ℝ) := by
  have hp : positive (shape 0 7 1) = false := by decide +kernel
  simp only [Z0_7_1Half, halfLaw, hp, Bool.false_eq_true, ite_false, if_false]
  split_ifs
  · exact Ball.exact_sound 1
  · exact Ball.exact_sound 0
  · exact Z0_7_1Probs_sound _
  · exact Z0_7_1Probs_sound _

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z0_7_1Half_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z0_7_1Half_sound_oai
