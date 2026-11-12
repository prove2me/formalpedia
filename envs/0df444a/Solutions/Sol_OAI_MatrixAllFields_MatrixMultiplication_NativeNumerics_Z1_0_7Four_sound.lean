-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z1_0_7Four_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:22:07.410514+00:00
-- url     : https://prove2.me/submissions/b5cd7215-366a-4cda-a8b8-9f3684d9004a

import Mathlib
import Definitions.Def_OAIQ254M011
import Definitions.Def_OAIQ254M012
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_inv_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_mul_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkLog_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_finSumBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_entropyTerm_ball
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_multLogs_sound

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
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
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

lemma product_fin6_enclosed (bs : Fin 6 → Fin 6 → Ball) (v : PairSlot → ℝ)
    (h : ∀ i j, (bs i j).Encloses (v (i,j))) :
    (finSumBall 6 (fun i => finSumBall 6 (bs i))).Encloses (∑ s : PairSlot, v s) := by
  rw [Fintype.sum_prod_type]
  exact finSumBall_sound 6 _ _ (fun i => finSumBall_sound 6 _ _ (h i))

lemma entropyTerm_zero_ball {p : ℝ} (hp : (Ball.exact 0).Encloses p) :
    (Ball.exact 0).Encloses (Foundation.entropyTerm p) := by
  have hb := Ball.bounds hp
  have h : p = 0 := by norm_num [Ball.lower, Ball.upper, Ball.exact] at hb <;> linarith
  simp only [h, Foundation.entropyTerm, neg_zero, zero_mul]
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

lemma forall_fin6 {P : Fin 6 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2)
    (h3 : P 3) (h4 : P 4) (h5 : P 5) : ∀ i, P i := by
  intro i
  fin_cases i <;> assumption

lemma pairSumBall_sound (bs : PairSlot → Ball) (v : PairSlot → ℝ)
    (h : ∀ a, (bs a).Encloses (v a)) :
    (pairSumBall bs).Encloses (∑ a, v a) := by
  exact product_fin6_enclosed _ _ (fun i j => h (i,j))

lemma entropyPair_enclosed (p : PairSlot → ℝ) (bs : PairSlot → Ball)
    (h : ∀ i, (bs i).Encloses (Foundation.entropyTerm (p i))) :
    (pairSumBall bs).Encloses (Foundation.finiteEntropy p) :=
  pairSumBall_sound _ _ h

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
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Four1_0_7
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
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
lemma Z1_0_7Raw_sound_0 (j : Fin 6) :
    (Z1_0_7Raw (0,j)).Encloses (weight (orderedPairInteger (shape 1 0 7) 0 j) : ℝ) := by
  fin_cases j
  · change (Z1_0_7Raw (0,0)).Encloses (weight (orderedPairInteger (shape 1 0 7) 0 0) : ℝ)
    have he : orderedPairInteger (shape 1 0 7) 0 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_0_7Raw (0,1)).Encloses (weight (orderedPairInteger (shape 1 0 7) 0 1) : ℝ)
    have he : orderedPairInteger (shape 1 0 7) 0 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_0_7Raw (0,2)).Encloses (weight (orderedPairInteger (shape 1 0 7) 0 2) : ℝ)
    have he : orderedPairInteger (shape 1 0 7) 0 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_0_7Raw (0,3)).Encloses (weight (orderedPairInteger (shape 1 0 7) 0 3) : ℝ)
    have he : orderedPairInteger (shape 1 0 7) 0 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_0_7Raw (0,4)).Encloses (weight (orderedPairInteger (shape 1 0 7) 0 4) : ℝ)
    have he : orderedPairInteger (shape 1 0 7) 0 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_0_7Raw (0,5)).Encloses (weight (orderedPairInteger (shape 1 0 7) 0 5) : ℝ)
    have he : orderedPairInteger (shape 1 0 7) 0 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z1_0_7Raw_sound_1 (j : Fin 6) :
    (Z1_0_7Raw (1,j)).Encloses (weight (orderedPairInteger (shape 1 0 7) 1 j) : ℝ) := by
  fin_cases j
  · change (Z1_0_7Raw (1,0)).Encloses (weight (orderedPairInteger (shape 1 0 7) 1 0) : ℝ)
    have he : orderedPairInteger (shape 1 0 7) 1 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_0_7Raw (1,1)).Encloses (weight (orderedPairInteger (shape 1 0 7) 1 1) : ℝ)
    have he : orderedPairInteger (shape 1 0 7) 1 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_0_7Raw (1,2)).Encloses (weight (orderedPairInteger (shape 1 0 7) 1 2) : ℝ)
    have he : orderedPairInteger (shape 1 0 7) 1 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_0_7Raw (1,3)).Encloses (weight (orderedPairInteger (shape 1 0 7) 1 3) : ℝ)
    have he : orderedPairInteger (shape 1 0 7) 1 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_0_7Raw (1,4)).Encloses (weight (orderedPairInteger (shape 1 0 7) 1 4) : ℝ)
    have he : orderedPairInteger (shape 1 0 7) 1 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_0_7Raw (1,5)).Encloses (weight (orderedPairInteger (shape 1 0 7) 1 5) : ℝ)
    have he : orderedPairInteger (shape 1 0 7) 1 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z1_0_7Raw_sound_2 (j : Fin 6) :
    (Z1_0_7Raw (2,j)).Encloses (weight (orderedPairInteger (shape 1 0 7) 2 j) : ℝ) := by
  fin_cases j
  · change (Z1_0_7Raw (2,0)).Encloses (weight (orderedPairInteger (shape 1 0 7) 2 0) : ℝ)
    have he : orderedPairInteger (shape 1 0 7) 2 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_0_7Raw (2,1)).Encloses (weight (orderedPairInteger (shape 1 0 7) 2 1) : ℝ)
    have he : orderedPairInteger (shape 1 0 7) 2 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_0_7Raw (2,2)).Encloses (weight (orderedPairInteger (shape 1 0 7) 2 2) : ℝ)
    have he : orderedPairInteger (shape 1 0 7) 2 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_0_7Raw (2,3)).Encloses (weight (orderedPairInteger (shape 1 0 7) 2 3) : ℝ)
    have he : orderedPairInteger (shape 1 0 7) 2 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_0_7Raw (2,4)).Encloses (weight (orderedPairInteger (shape 1 0 7) 2 4) : ℝ)
    have he : orderedPairInteger (shape 1 0 7) 2 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_0_7Raw (2,5)).Encloses (weight (orderedPairInteger (shape 1 0 7) 2 5) : ℝ)
    have he : orderedPairInteger (shape 1 0 7) 2 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z1_0_7Raw_sound_3 (j : Fin 6) :
    (Z1_0_7Raw (3,j)).Encloses (weight (orderedPairInteger (shape 1 0 7) 3 j) : ℝ) := by
  fin_cases j
  · change (Z1_0_7Raw (3,0)).Encloses (weight (orderedPairInteger (shape 1 0 7) 3 0) : ℝ)
    have he : orderedPairInteger (shape 1 0 7) 3 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_0_7Raw (3,1)).Encloses (weight (orderedPairInteger (shape 1 0 7) 3 1) : ℝ)
    have he : orderedPairInteger (shape 1 0 7) 3 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_0_7Raw (3,2)).Encloses (weight (orderedPairInteger (shape 1 0 7) 3 2) : ℝ)
    have he : orderedPairInteger (shape 1 0 7) 3 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_0_7Raw (3,3)).Encloses (weight (orderedPairInteger (shape 1 0 7) 3 3) : ℝ)
    have he : orderedPairInteger (shape 1 0 7) 3 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_0_7Raw (3,4)).Encloses (weight (orderedPairInteger (shape 1 0 7) 3 4) : ℝ)
    have he : orderedPairInteger (shape 1 0 7) 3 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_0_7Raw (3,5)).Encloses (weight (orderedPairInteger (shape 1 0 7) 3 5) : ℝ)
    have he : orderedPairInteger (shape 1 0 7) 3 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z1_0_7Raw_sound_4 (j : Fin 6) :
    (Z1_0_7Raw (4,j)).Encloses (weight (orderedPairInteger (shape 1 0 7) 4 j) : ℝ) := by
  fin_cases j
  · change (Z1_0_7Raw (4,0)).Encloses (weight (orderedPairInteger (shape 1 0 7) 4 0) : ℝ)
    have he : orderedPairInteger (shape 1 0 7) 4 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_0_7Raw (4,1)).Encloses (weight (orderedPairInteger (shape 1 0 7) 4 1) : ℝ)
    have he : orderedPairInteger (shape 1 0 7) 4 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_0_7Raw (4,2)).Encloses (weight (orderedPairInteger (shape 1 0 7) 4 2) : ℝ)
    have he : orderedPairInteger (shape 1 0 7) 4 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_0_7Raw (4,3)).Encloses (weight (orderedPairInteger (shape 1 0 7) 4 3) : ℝ)
    have he : orderedPairInteger (shape 1 0 7) 4 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_0_7Raw (4,4)).Encloses (weight (orderedPairInteger (shape 1 0 7) 4 4) : ℝ)
    have he : orderedPairInteger (shape 1 0 7) 4 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_0_7Raw (4,5)).Encloses (weight (orderedPairInteger (shape 1 0 7) 4 5) : ℝ)
    have he : orderedPairInteger (shape 1 0 7) 4 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z1_0_7Raw_sound_5 (j : Fin 6) :
    (Z1_0_7Raw (5,j)).Encloses (weight (orderedPairInteger (shape 1 0 7) 5 j) : ℝ) := by
  fin_cases j
  · change (Z1_0_7Raw (5,0)).Encloses (weight (orderedPairInteger (shape 1 0 7) 5 0) : ℝ)
    have he : orderedPairInteger (shape 1 0 7) 5 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_0_7Raw (5,1)).Encloses (weight (orderedPairInteger (shape 1 0 7) 5 1) : ℝ)
    have he : orderedPairInteger (shape 1 0 7) 5 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_0_7Raw (5,2)).Encloses (weight (orderedPairInteger (shape 1 0 7) 5 2) : ℝ)
    have he : orderedPairInteger (shape 1 0 7) 5 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_0_7Raw (5,3)).Encloses (weight (orderedPairInteger (shape 1 0 7) 5 3) : ℝ)
    have he : orderedPairInteger (shape 1 0 7) 5 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_0_7Raw (5,4)).Encloses (weight (orderedPairInteger (shape 1 0 7) 5 4) : ℝ)
    have he : orderedPairInteger (shape 1 0 7) 5 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_0_7Raw (5,5)).Encloses (weight (orderedPairInteger (shape 1 0 7) 5 5) : ℝ)
    have he : orderedPairInteger (shape 1 0 7) 5 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z1_0_7Raw_sound (ij : PairSlot) :
    (Z1_0_7Raw ij).Encloses (weight (orderedPairInteger (shape 1 0 7) ij.1 ij.2) : ℝ) := by
  rcases ij with ⟨i,j⟩
  revert i
  exact forall_fin6 (Z1_0_7Raw_sound_0 j) (Z1_0_7Raw_sound_1 j) (Z1_0_7Raw_sound_2 j) (Z1_0_7Raw_sound_3 j) (Z1_0_7Raw_sound_4 j) (Z1_0_7Raw_sound_5 j)
lemma Z1_0_7Den_sound : Z1_0_7Den.Encloses
    (((orderedPairs (shape 1 0 7)).map (fun ij => weight (orderedPairInteger (shape 1 0 7) ij.1 ij.2))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (orderedPairs (shape 1 0 7)) Z1_0_7Raw
    (fun ij => weight (orderedPairInteger (shape 1 0 7) ij.1 ij.2))
    (fun ij _ => Z1_0_7Raw_sound ij)) (by decide +kernel)
lemma Z1_0_7Den_pos : 0 < Z1_0_7Den.lower := by decide +kernel
lemma Z1_0_7Contains : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j = shapeMax (shape 1 0 7) →
    contains (.mul (Z1_0_7Raw (i,j)) (.inv Z1_0_7Den)) (Z1_0_7Probs (i,j)) = true := by
  decide +kernel
lemma Z1_0_7Zero : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j ≠ shapeMax (shape 1 0 7) → Z1_0_7Probs (i,j) = .exact 0 := by
  decide +kernel
lemma Z1_0_7Probs_sound (ij : PairSlot) :
    (Z1_0_7Probs ij).Encloses (zeroPairLaw (shape 1 0 7) ij.1 ij.2 : ℝ) := by
  by_cases h : statisticWeight ij.1 + statisticWeight ij.2 = shapeMax (shape 1 0 7)
  · have hb := contains_sound (Ball.mul_sound (Z1_0_7Raw_sound ij)
      (Ball.inv_sound Z1_0_7Den_sound Z1_0_7Den_pos)) (Z1_0_7Contains ij.1 ij.2 h)
    simpa only [zeroPairLaw, h, ite_true, if_true, Rat.cast_div, Rat.cast_mul,
      Rat.cast_inv, div_eq_mul_inv] using hb
  · rw [Z1_0_7Zero ij.1 ij.2 h]
    simpa only [zeroPairLaw, h, ite_false, if_false] using Ball.exact_sound 0

lemma Z1_0_7E_4_5Log_sound : Z1_0_7E_4_5Log.Encloses (Real.log (Z1_0_7Value ((4,5) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z1_0_7Probs_sound ((4,5) : PairSlot)) (w := Z1_0_7E_4_5LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z1_0_7E_4_5_sound : Z1_0_7E_4_5.Encloses (Foundation.entropyTerm (Z1_0_7Value ((4,5) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z1_0_7Probs_sound ((4,5) : PairSlot)) Z1_0_7E_4_5Log_sound) (by decide +kernel)
lemma Z1_0_7E_5_4Log_sound : Z1_0_7E_5_4Log.Encloses (Real.log (Z1_0_7Value ((5,4) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z1_0_7Probs_sound ((5,4) : PairSlot)) (w := Z1_0_7E_5_4LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z1_0_7E_5_4_sound : Z1_0_7E_5_4.Encloses (Foundation.entropyTerm (Z1_0_7Value ((5,4) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z1_0_7Probs_sound ((5,4) : PairSlot)) Z1_0_7E_5_4Log_sound) (by decide +kernel)
lemma Z1_0_7Terms_sound (a : PairSlot) :
    (Z1_0_7Terms a).Encloses (Foundation.entropyTerm (Z1_0_7Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (entropyTerm_zero_ball (Z1_0_7Probs_sound ((0,0) : PairSlot))) (entropyTerm_zero_ball (Z1_0_7Probs_sound ((0,1) : PairSlot))) (entropyTerm_zero_ball (Z1_0_7Probs_sound ((0,2) : PairSlot))) (entropyTerm_zero_ball (Z1_0_7Probs_sound ((0,3) : PairSlot))) (entropyTerm_zero_ball (Z1_0_7Probs_sound ((0,4) : PairSlot))) (entropyTerm_zero_ball (Z1_0_7Probs_sound ((0,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z1_0_7Probs_sound ((1,0) : PairSlot))) (entropyTerm_zero_ball (Z1_0_7Probs_sound ((1,1) : PairSlot))) (entropyTerm_zero_ball (Z1_0_7Probs_sound ((1,2) : PairSlot))) (entropyTerm_zero_ball (Z1_0_7Probs_sound ((1,3) : PairSlot))) (entropyTerm_zero_ball (Z1_0_7Probs_sound ((1,4) : PairSlot))) (entropyTerm_zero_ball (Z1_0_7Probs_sound ((1,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z1_0_7Probs_sound ((2,0) : PairSlot))) (entropyTerm_zero_ball (Z1_0_7Probs_sound ((2,1) : PairSlot))) (entropyTerm_zero_ball (Z1_0_7Probs_sound ((2,2) : PairSlot))) (entropyTerm_zero_ball (Z1_0_7Probs_sound ((2,3) : PairSlot))) (entropyTerm_zero_ball (Z1_0_7Probs_sound ((2,4) : PairSlot))) (entropyTerm_zero_ball (Z1_0_7Probs_sound ((2,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z1_0_7Probs_sound ((3,0) : PairSlot))) (entropyTerm_zero_ball (Z1_0_7Probs_sound ((3,1) : PairSlot))) (entropyTerm_zero_ball (Z1_0_7Probs_sound ((3,2) : PairSlot))) (entropyTerm_zero_ball (Z1_0_7Probs_sound ((3,3) : PairSlot))) (entropyTerm_zero_ball (Z1_0_7Probs_sound ((3,4) : PairSlot))) (entropyTerm_zero_ball (Z1_0_7Probs_sound ((3,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z1_0_7Probs_sound ((4,0) : PairSlot))) (entropyTerm_zero_ball (Z1_0_7Probs_sound ((4,1) : PairSlot))) (entropyTerm_zero_ball (Z1_0_7Probs_sound ((4,2) : PairSlot))) (entropyTerm_zero_ball (Z1_0_7Probs_sound ((4,3) : PairSlot))) (entropyTerm_zero_ball (Z1_0_7Probs_sound ((4,4) : PairSlot))) Z1_0_7E_4_5_sound
  · exact forall_fin6 (entropyTerm_zero_ball (Z1_0_7Probs_sound ((5,0) : PairSlot))) (entropyTerm_zero_ball (Z1_0_7Probs_sound ((5,1) : PairSlot))) (entropyTerm_zero_ball (Z1_0_7Probs_sound ((5,2) : PairSlot))) (entropyTerm_zero_ball (Z1_0_7Probs_sound ((5,3) : PairSlot))) Z1_0_7E_5_4_sound (entropyTerm_zero_ball (Z1_0_7Probs_sound ((5,5) : PairSlot)))
lemma Z1_0_7Entropy_sound : Z1_0_7Entropy.Encloses (Foundation.finiteEntropy Z1_0_7Value) := by
  exact contains_sound (entropyPair_enclosed Z1_0_7Value Z1_0_7Terms Z1_0_7Terms_sound) (by decide +kernel)
lemma Z1_0_7Labels_sound : Z1_0_7Labels.Encloses
    (∑ a : PairSlot, (zeroPairLaw (shape 1 0 7) a.1 a.2 : ℝ) *
      Real.log (AllFieldParameters.multiplicity a.1 * AllFieldParameters.multiplicity a.2 : ℕ)) := by
  exact contains_sound (pairSumBall_sound (fun a => .mul (Z1_0_7Probs a) (multLogs a))
    _ (fun a => Ball.mul_sound (Z1_0_7Probs_sound a) (multLogs_sound a))) (by decide +kernel)
lemma Z1_0_7Four_sound_oai : Z1_0_7Four.Encloses (AllFieldZeroLeafRates.fourRate (shape 1 0 7)) := by
  exact contains_sound (Ball.add_sound Z1_0_7Entropy_sound Z1_0_7Labels_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z1_0_7Four_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z1_0_7Four_sound_oai
