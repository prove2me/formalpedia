-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.fourRateBalls_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:59:29.835352+00:00
-- url     : https://prove2.me/submissions/b67f2854-71b5-4433-b376-c304837ba442

import Mathlib
import Definitions.Def_OAIQ254M006
import Definitions.Def_OAIQ254M011
import Definitions.Def_OAIQ254M012
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_inv_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_mul_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkLog_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkPolynomial_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_finSumBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_Z0_1_7Probs_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_Z0_3_5Four_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_Z0_4_4Four_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_Z0_5_3Four_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_Z0_6_2Probs_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_Z0_7_1Four_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_Z0_8_0Four_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_Z1_0_7Four_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_Z1_7_0Four_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_Z2_0_6Four_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_Z2_6_0Four_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_Z3_0_5Four_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_Z3_5_0Four_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_Z4_0_4Four_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_Z4_4_0Four_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_Z5_0_3Four_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_Z5_3_0Four_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_Z6_0_2Four_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_Z6_2_0Four_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_Z7_0_1Four_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_Z7_1_0Four_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_Z8_0_0Four_sound
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

lemma exponential_polynomial_cast (n : ℤ) :
    (((∑ j ∈ Finset.range 17, ((n : ℚ) / 640000) ^ j /
      Nat.factorial j : ℚ) : ℝ)) =
    polynomial (((n : ℚ) / 640000 : ℚ) : ℝ) exponentialCoefficients := by
  simp only [Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast]
  norm_num [Finset.sum_range_succ, exponentialCoefficients, List.range_succ,
    polynomial, List.map_append]
  ring

lemma weight_enclosed_of_trace (n : ℤ) (trace : List Ball)
    (b₁ b₂ b₃ b₄ b₅ b₆ : Ball)
    (hp : checkPolynomial (.exact ((n : ℚ) / 640000))
      exponentialCoefficients trace = true)
    (h₁ : contains (.mul (traceHead trace) (traceHead trace)) b₁ = true)
    (h₂ : contains (.mul b₁ b₁) b₂ = true)
    (h₃ : contains (.mul b₂ b₂) b₃ = true)
    (h₄ : contains (.mul b₃ b₃) b₄ = true)
    (h₅ : contains (.mul b₄ b₄) b₅ = true)
    (h₆ : contains (.mul b₅ b₅) b₆ = true) :
    b₆.Encloses (weight n : ℝ) := by
  have p := checkPolynomial_sound (Ball.exact_sound ((n : ℚ) / 640000))
    exponentialCoefficients trace hp
  rw [← exponential_polynomial_cast] at p
  have p₁ := contains_sound (Ball.mul_sound p p) h₁
  have p₂ := contains_sound (Ball.mul_sound p₁ p₁) h₂
  have p₃ := contains_sound (Ball.mul_sound p₂ p₂) h₃
  have p₄ := contains_sound (Ball.mul_sound p₃ p₃) h₄
  have p₅ := contains_sound (Ball.mul_sound p₄ p₄) h₅
  have p₆ := contains_sound (Ball.mul_sound p₅ p₅) h₆
  convert p₆ using 1
  all_goals try with_reducible_and_instances rfl
  simp only [weight, Rat.cast_pow]
  ring

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

lemma log_exact_one_ball {p : ℝ} (hp : (Ball.exact 1).Encloses p) :
    (Ball.exact 0).Encloses (Real.log p) := by
  have hb := Ball.bounds hp
  have h : p = 1 := by norm_num [Ball.lower, Ball.upper, Ball.exact] at hb <;> linarith
  rw [h, Real.log_one]
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
open AllFieldInitialEntropyCertificate
open scoped BigOperators
lemma w195_sound : w195.Encloses (weight 0 : ℝ) := by
  have he : weight 0 = 1 := by decide +kernel
  rw [he, Rat.cast_one]
  simpa only [w195, Rat.cast_one] using Ball.exact_sound 1

end MatrixMultiplication.NativeNumerics

namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
lemma Z0_0_8Raw_sound_0 (j : Fin 6) :
    (Z0_0_8Raw (0,j)).Encloses (weight (orderedPairInteger (shape 0 0 8) 0 j) : ℝ) := by
  fin_cases j
  · change (Z0_0_8Raw (0,0)).Encloses (weight (orderedPairInteger (shape 0 0 8) 0 0) : ℝ)
    have he : orderedPairInteger (shape 0 0 8) 0 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_0_8Raw (0,1)).Encloses (weight (orderedPairInteger (shape 0 0 8) 0 1) : ℝ)
    have he : orderedPairInteger (shape 0 0 8) 0 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_0_8Raw (0,2)).Encloses (weight (orderedPairInteger (shape 0 0 8) 0 2) : ℝ)
    have he : orderedPairInteger (shape 0 0 8) 0 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_0_8Raw (0,3)).Encloses (weight (orderedPairInteger (shape 0 0 8) 0 3) : ℝ)
    have he : orderedPairInteger (shape 0 0 8) 0 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_0_8Raw (0,4)).Encloses (weight (orderedPairInteger (shape 0 0 8) 0 4) : ℝ)
    have he : orderedPairInteger (shape 0 0 8) 0 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_0_8Raw (0,5)).Encloses (weight (orderedPairInteger (shape 0 0 8) 0 5) : ℝ)
    have he : orderedPairInteger (shape 0 0 8) 0 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_0_8Raw_sound_1 (j : Fin 6) :
    (Z0_0_8Raw (1,j)).Encloses (weight (orderedPairInteger (shape 0 0 8) 1 j) : ℝ) := by
  fin_cases j
  · change (Z0_0_8Raw (1,0)).Encloses (weight (orderedPairInteger (shape 0 0 8) 1 0) : ℝ)
    have he : orderedPairInteger (shape 0 0 8) 1 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_0_8Raw (1,1)).Encloses (weight (orderedPairInteger (shape 0 0 8) 1 1) : ℝ)
    have he : orderedPairInteger (shape 0 0 8) 1 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_0_8Raw (1,2)).Encloses (weight (orderedPairInteger (shape 0 0 8) 1 2) : ℝ)
    have he : orderedPairInteger (shape 0 0 8) 1 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_0_8Raw (1,3)).Encloses (weight (orderedPairInteger (shape 0 0 8) 1 3) : ℝ)
    have he : orderedPairInteger (shape 0 0 8) 1 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_0_8Raw (1,4)).Encloses (weight (orderedPairInteger (shape 0 0 8) 1 4) : ℝ)
    have he : orderedPairInteger (shape 0 0 8) 1 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_0_8Raw (1,5)).Encloses (weight (orderedPairInteger (shape 0 0 8) 1 5) : ℝ)
    have he : orderedPairInteger (shape 0 0 8) 1 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_0_8Raw_sound_2 (j : Fin 6) :
    (Z0_0_8Raw (2,j)).Encloses (weight (orderedPairInteger (shape 0 0 8) 2 j) : ℝ) := by
  fin_cases j
  · change (Z0_0_8Raw (2,0)).Encloses (weight (orderedPairInteger (shape 0 0 8) 2 0) : ℝ)
    have he : orderedPairInteger (shape 0 0 8) 2 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_0_8Raw (2,1)).Encloses (weight (orderedPairInteger (shape 0 0 8) 2 1) : ℝ)
    have he : orderedPairInteger (shape 0 0 8) 2 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_0_8Raw (2,2)).Encloses (weight (orderedPairInteger (shape 0 0 8) 2 2) : ℝ)
    have he : orderedPairInteger (shape 0 0 8) 2 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_0_8Raw (2,3)).Encloses (weight (orderedPairInteger (shape 0 0 8) 2 3) : ℝ)
    have he : orderedPairInteger (shape 0 0 8) 2 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_0_8Raw (2,4)).Encloses (weight (orderedPairInteger (shape 0 0 8) 2 4) : ℝ)
    have he : orderedPairInteger (shape 0 0 8) 2 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_0_8Raw (2,5)).Encloses (weight (orderedPairInteger (shape 0 0 8) 2 5) : ℝ)
    have he : orderedPairInteger (shape 0 0 8) 2 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_0_8Raw_sound_3 (j : Fin 6) :
    (Z0_0_8Raw (3,j)).Encloses (weight (orderedPairInteger (shape 0 0 8) 3 j) : ℝ) := by
  fin_cases j
  · change (Z0_0_8Raw (3,0)).Encloses (weight (orderedPairInteger (shape 0 0 8) 3 0) : ℝ)
    have he : orderedPairInteger (shape 0 0 8) 3 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_0_8Raw (3,1)).Encloses (weight (orderedPairInteger (shape 0 0 8) 3 1) : ℝ)
    have he : orderedPairInteger (shape 0 0 8) 3 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_0_8Raw (3,2)).Encloses (weight (orderedPairInteger (shape 0 0 8) 3 2) : ℝ)
    have he : orderedPairInteger (shape 0 0 8) 3 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_0_8Raw (3,3)).Encloses (weight (orderedPairInteger (shape 0 0 8) 3 3) : ℝ)
    have he : orderedPairInteger (shape 0 0 8) 3 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_0_8Raw (3,4)).Encloses (weight (orderedPairInteger (shape 0 0 8) 3 4) : ℝ)
    have he : orderedPairInteger (shape 0 0 8) 3 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_0_8Raw (3,5)).Encloses (weight (orderedPairInteger (shape 0 0 8) 3 5) : ℝ)
    have he : orderedPairInteger (shape 0 0 8) 3 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_0_8Raw_sound_4 (j : Fin 6) :
    (Z0_0_8Raw (4,j)).Encloses (weight (orderedPairInteger (shape 0 0 8) 4 j) : ℝ) := by
  fin_cases j
  · change (Z0_0_8Raw (4,0)).Encloses (weight (orderedPairInteger (shape 0 0 8) 4 0) : ℝ)
    have he : orderedPairInteger (shape 0 0 8) 4 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_0_8Raw (4,1)).Encloses (weight (orderedPairInteger (shape 0 0 8) 4 1) : ℝ)
    have he : orderedPairInteger (shape 0 0 8) 4 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_0_8Raw (4,2)).Encloses (weight (orderedPairInteger (shape 0 0 8) 4 2) : ℝ)
    have he : orderedPairInteger (shape 0 0 8) 4 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_0_8Raw (4,3)).Encloses (weight (orderedPairInteger (shape 0 0 8) 4 3) : ℝ)
    have he : orderedPairInteger (shape 0 0 8) 4 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_0_8Raw (4,4)).Encloses (weight (orderedPairInteger (shape 0 0 8) 4 4) : ℝ)
    have he : orderedPairInteger (shape 0 0 8) 4 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_0_8Raw (4,5)).Encloses (weight (orderedPairInteger (shape 0 0 8) 4 5) : ℝ)
    have he : orderedPairInteger (shape 0 0 8) 4 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_0_8Raw_sound_5 (j : Fin 6) :
    (Z0_0_8Raw (5,j)).Encloses (weight (orderedPairInteger (shape 0 0 8) 5 j) : ℝ) := by
  fin_cases j
  · change (Z0_0_8Raw (5,0)).Encloses (weight (orderedPairInteger (shape 0 0 8) 5 0) : ℝ)
    have he : orderedPairInteger (shape 0 0 8) 5 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_0_8Raw (5,1)).Encloses (weight (orderedPairInteger (shape 0 0 8) 5 1) : ℝ)
    have he : orderedPairInteger (shape 0 0 8) 5 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_0_8Raw (5,2)).Encloses (weight (orderedPairInteger (shape 0 0 8) 5 2) : ℝ)
    have he : orderedPairInteger (shape 0 0 8) 5 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_0_8Raw (5,3)).Encloses (weight (orderedPairInteger (shape 0 0 8) 5 3) : ℝ)
    have he : orderedPairInteger (shape 0 0 8) 5 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_0_8Raw (5,4)).Encloses (weight (orderedPairInteger (shape 0 0 8) 5 4) : ℝ)
    have he : orderedPairInteger (shape 0 0 8) 5 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_0_8Raw (5,5)).Encloses (weight (orderedPairInteger (shape 0 0 8) 5 5) : ℝ)
    have he : orderedPairInteger (shape 0 0 8) 5 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_0_8Raw_sound (ij : PairSlot) :
    (Z0_0_8Raw ij).Encloses (weight (orderedPairInteger (shape 0 0 8) ij.1 ij.2) : ℝ) := by
  rcases ij with ⟨i,j⟩
  revert i
  exact forall_fin6 (Z0_0_8Raw_sound_0 j) (Z0_0_8Raw_sound_1 j) (Z0_0_8Raw_sound_2 j) (Z0_0_8Raw_sound_3 j) (Z0_0_8Raw_sound_4 j) (Z0_0_8Raw_sound_5 j)
lemma Z0_0_8Den_sound : Z0_0_8Den.Encloses
    (((orderedPairs (shape 0 0 8)).map (fun ij => weight (orderedPairInteger (shape 0 0 8) ij.1 ij.2))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (orderedPairs (shape 0 0 8)) Z0_0_8Raw
    (fun ij => weight (orderedPairInteger (shape 0 0 8) ij.1 ij.2))
    (fun ij _ => Z0_0_8Raw_sound ij)) (by decide +kernel)
lemma Z0_0_8Den_pos : 0 < Z0_0_8Den.lower := by decide +kernel
lemma Z0_0_8Contains : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j = shapeMax (shape 0 0 8) →
    contains (.mul (Z0_0_8Raw (i,j)) (.inv Z0_0_8Den)) (Z0_0_8Probs (i,j)) = true := by
  decide +kernel
lemma Z0_0_8Zero : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j ≠ shapeMax (shape 0 0 8) → Z0_0_8Probs (i,j) = .exact 0 := by
  decide +kernel
lemma Z0_0_8Probs_sound (ij : PairSlot) :
    (Z0_0_8Probs ij).Encloses (zeroPairLaw (shape 0 0 8) ij.1 ij.2 : ℝ) := by
  by_cases h : statisticWeight ij.1 + statisticWeight ij.2 = shapeMax (shape 0 0 8)
  · have hb := contains_sound (Ball.mul_sound (Z0_0_8Raw_sound ij)
      (Ball.inv_sound Z0_0_8Den_sound Z0_0_8Den_pos)) (Z0_0_8Contains ij.1 ij.2 h)
    simpa only [zeroPairLaw, h, ite_true, if_true, Rat.cast_div, Rat.cast_mul,
      Rat.cast_inv, div_eq_mul_inv] using hb
  · rw [Z0_0_8Zero ij.1 ij.2 h]
    simpa only [zeroPairLaw, h, ite_false, if_false] using Ball.exact_sound 0

lemma Z0_0_8E_5_5Log_sound : Z0_0_8E_5_5Log.Encloses (Real.log (Z0_0_8Value ((5,5) : PairSlot))) := by
  exact log_exact_one_ball (Z0_0_8Probs_sound ((5,5) : PairSlot))
lemma Z0_0_8E_5_5_sound : Z0_0_8E_5_5.Encloses (Foundation.entropyTerm (Z0_0_8Value ((5,5) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z0_0_8Probs_sound ((5,5) : PairSlot)) Z0_0_8E_5_5Log_sound) (by decide +kernel)
lemma Z0_0_8Terms_sound (a : PairSlot) :
    (Z0_0_8Terms a).Encloses (Foundation.entropyTerm (Z0_0_8Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (entropyTerm_zero_ball (Z0_0_8Probs_sound ((0,0) : PairSlot))) (entropyTerm_zero_ball (Z0_0_8Probs_sound ((0,1) : PairSlot))) (entropyTerm_zero_ball (Z0_0_8Probs_sound ((0,2) : PairSlot))) (entropyTerm_zero_ball (Z0_0_8Probs_sound ((0,3) : PairSlot))) (entropyTerm_zero_ball (Z0_0_8Probs_sound ((0,4) : PairSlot))) (entropyTerm_zero_ball (Z0_0_8Probs_sound ((0,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z0_0_8Probs_sound ((1,0) : PairSlot))) (entropyTerm_zero_ball (Z0_0_8Probs_sound ((1,1) : PairSlot))) (entropyTerm_zero_ball (Z0_0_8Probs_sound ((1,2) : PairSlot))) (entropyTerm_zero_ball (Z0_0_8Probs_sound ((1,3) : PairSlot))) (entropyTerm_zero_ball (Z0_0_8Probs_sound ((1,4) : PairSlot))) (entropyTerm_zero_ball (Z0_0_8Probs_sound ((1,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z0_0_8Probs_sound ((2,0) : PairSlot))) (entropyTerm_zero_ball (Z0_0_8Probs_sound ((2,1) : PairSlot))) (entropyTerm_zero_ball (Z0_0_8Probs_sound ((2,2) : PairSlot))) (entropyTerm_zero_ball (Z0_0_8Probs_sound ((2,3) : PairSlot))) (entropyTerm_zero_ball (Z0_0_8Probs_sound ((2,4) : PairSlot))) (entropyTerm_zero_ball (Z0_0_8Probs_sound ((2,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z0_0_8Probs_sound ((3,0) : PairSlot))) (entropyTerm_zero_ball (Z0_0_8Probs_sound ((3,1) : PairSlot))) (entropyTerm_zero_ball (Z0_0_8Probs_sound ((3,2) : PairSlot))) (entropyTerm_zero_ball (Z0_0_8Probs_sound ((3,3) : PairSlot))) (entropyTerm_zero_ball (Z0_0_8Probs_sound ((3,4) : PairSlot))) (entropyTerm_zero_ball (Z0_0_8Probs_sound ((3,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z0_0_8Probs_sound ((4,0) : PairSlot))) (entropyTerm_zero_ball (Z0_0_8Probs_sound ((4,1) : PairSlot))) (entropyTerm_zero_ball (Z0_0_8Probs_sound ((4,2) : PairSlot))) (entropyTerm_zero_ball (Z0_0_8Probs_sound ((4,3) : PairSlot))) (entropyTerm_zero_ball (Z0_0_8Probs_sound ((4,4) : PairSlot))) (entropyTerm_zero_ball (Z0_0_8Probs_sound ((4,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z0_0_8Probs_sound ((5,0) : PairSlot))) (entropyTerm_zero_ball (Z0_0_8Probs_sound ((5,1) : PairSlot))) (entropyTerm_zero_ball (Z0_0_8Probs_sound ((5,2) : PairSlot))) (entropyTerm_zero_ball (Z0_0_8Probs_sound ((5,3) : PairSlot))) (entropyTerm_zero_ball (Z0_0_8Probs_sound ((5,4) : PairSlot))) Z0_0_8E_5_5_sound
lemma Z0_0_8Entropy_sound : Z0_0_8Entropy.Encloses (Foundation.finiteEntropy Z0_0_8Value) := by
  exact contains_sound (entropyPair_enclosed Z0_0_8Value Z0_0_8Terms Z0_0_8Terms_sound) (by decide +kernel)
lemma Z0_0_8Labels_sound : Z0_0_8Labels.Encloses
    (∑ a : PairSlot, (zeroPairLaw (shape 0 0 8) a.1 a.2 : ℝ) *
      Real.log (AllFieldParameters.multiplicity a.1 * AllFieldParameters.multiplicity a.2 : ℕ)) := by
  exact contains_sound (pairSumBall_sound (fun a => .mul (Z0_0_8Probs a) (multLogs a))
    _ (fun a => Ball.mul_sound (Z0_0_8Probs_sound a) (multLogs_sound a))) (by decide +kernel)
lemma Z0_0_8Four_sound : Z0_0_8Four.Encloses (AllFieldZeroLeafRates.fourRate (shape 0 0 8)) := by
  exact contains_sound (Ball.add_sound Z0_0_8Entropy_sound Z0_0_8Labels_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Four0_1_7
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
lemma Z0_1_7E_4_5Log_sound : Z0_1_7E_4_5Log.Encloses (Real.log (Z0_1_7Value ((4,5) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z0_1_7Probs_sound ((4,5) : PairSlot)) (w := Z0_1_7E_4_5LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z0_1_7E_4_5_sound : Z0_1_7E_4_5.Encloses (Foundation.entropyTerm (Z0_1_7Value ((4,5) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z0_1_7Probs_sound ((4,5) : PairSlot)) Z0_1_7E_4_5Log_sound) (by decide +kernel)
lemma Z0_1_7E_5_4Log_sound : Z0_1_7E_5_4Log.Encloses (Real.log (Z0_1_7Value ((5,4) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z0_1_7Probs_sound ((5,4) : PairSlot)) (w := Z0_1_7E_5_4LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z0_1_7E_5_4_sound : Z0_1_7E_5_4.Encloses (Foundation.entropyTerm (Z0_1_7Value ((5,4) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z0_1_7Probs_sound ((5,4) : PairSlot)) Z0_1_7E_5_4Log_sound) (by decide +kernel)
lemma Z0_1_7Terms_sound (a : PairSlot) :
    (Z0_1_7Terms a).Encloses (Foundation.entropyTerm (Z0_1_7Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (entropyTerm_zero_ball (Z0_1_7Probs_sound ((0,0) : PairSlot))) (entropyTerm_zero_ball (Z0_1_7Probs_sound ((0,1) : PairSlot))) (entropyTerm_zero_ball (Z0_1_7Probs_sound ((0,2) : PairSlot))) (entropyTerm_zero_ball (Z0_1_7Probs_sound ((0,3) : PairSlot))) (entropyTerm_zero_ball (Z0_1_7Probs_sound ((0,4) : PairSlot))) (entropyTerm_zero_ball (Z0_1_7Probs_sound ((0,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z0_1_7Probs_sound ((1,0) : PairSlot))) (entropyTerm_zero_ball (Z0_1_7Probs_sound ((1,1) : PairSlot))) (entropyTerm_zero_ball (Z0_1_7Probs_sound ((1,2) : PairSlot))) (entropyTerm_zero_ball (Z0_1_7Probs_sound ((1,3) : PairSlot))) (entropyTerm_zero_ball (Z0_1_7Probs_sound ((1,4) : PairSlot))) (entropyTerm_zero_ball (Z0_1_7Probs_sound ((1,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z0_1_7Probs_sound ((2,0) : PairSlot))) (entropyTerm_zero_ball (Z0_1_7Probs_sound ((2,1) : PairSlot))) (entropyTerm_zero_ball (Z0_1_7Probs_sound ((2,2) : PairSlot))) (entropyTerm_zero_ball (Z0_1_7Probs_sound ((2,3) : PairSlot))) (entropyTerm_zero_ball (Z0_1_7Probs_sound ((2,4) : PairSlot))) (entropyTerm_zero_ball (Z0_1_7Probs_sound ((2,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z0_1_7Probs_sound ((3,0) : PairSlot))) (entropyTerm_zero_ball (Z0_1_7Probs_sound ((3,1) : PairSlot))) (entropyTerm_zero_ball (Z0_1_7Probs_sound ((3,2) : PairSlot))) (entropyTerm_zero_ball (Z0_1_7Probs_sound ((3,3) : PairSlot))) (entropyTerm_zero_ball (Z0_1_7Probs_sound ((3,4) : PairSlot))) (entropyTerm_zero_ball (Z0_1_7Probs_sound ((3,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z0_1_7Probs_sound ((4,0) : PairSlot))) (entropyTerm_zero_ball (Z0_1_7Probs_sound ((4,1) : PairSlot))) (entropyTerm_zero_ball (Z0_1_7Probs_sound ((4,2) : PairSlot))) (entropyTerm_zero_ball (Z0_1_7Probs_sound ((4,3) : PairSlot))) (entropyTerm_zero_ball (Z0_1_7Probs_sound ((4,4) : PairSlot))) Z0_1_7E_4_5_sound
  · exact forall_fin6 (entropyTerm_zero_ball (Z0_1_7Probs_sound ((5,0) : PairSlot))) (entropyTerm_zero_ball (Z0_1_7Probs_sound ((5,1) : PairSlot))) (entropyTerm_zero_ball (Z0_1_7Probs_sound ((5,2) : PairSlot))) (entropyTerm_zero_ball (Z0_1_7Probs_sound ((5,3) : PairSlot))) Z0_1_7E_5_4_sound (entropyTerm_zero_ball (Z0_1_7Probs_sound ((5,5) : PairSlot)))
lemma Z0_1_7Entropy_sound : Z0_1_7Entropy.Encloses (Foundation.finiteEntropy Z0_1_7Value) := by
  exact contains_sound (entropyPair_enclosed Z0_1_7Value Z0_1_7Terms Z0_1_7Terms_sound) (by decide +kernel)
lemma Z0_1_7Labels_sound : Z0_1_7Labels.Encloses
    (∑ a : PairSlot, (zeroPairLaw (shape 0 1 7) a.1 a.2 : ℝ) *
      Real.log (AllFieldParameters.multiplicity a.1 * AllFieldParameters.multiplicity a.2 : ℕ)) := by
  exact contains_sound (pairSumBall_sound (fun a => .mul (Z0_1_7Probs a) (multLogs a))
    _ (fun a => Ball.mul_sound (Z0_1_7Probs_sound a) (multLogs_sound a))) (by decide +kernel)
lemma Z0_1_7Four_sound : Z0_1_7Four.Encloses (AllFieldZeroLeafRates.fourRate (shape 0 1 7)) := by
  exact contains_sound (Ball.add_sound Z0_1_7Entropy_sound Z0_1_7Labels_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

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
lemma zeroSecond_list : zeroSecond = [
  (shape 0 0 8),
  (shape 0 1 7),
  (shape 0 2 6),
  (shape 0 3 5),
  (shape 0 4 4),
  (shape 0 5 3),
  (shape 0 6 2),
  (shape 0 7 1),
  (shape 0 8 0),
  (shape 1 0 7),
  (shape 1 7 0),
  (shape 2 0 6),
  (shape 2 6 0),
  (shape 3 0 5),
  (shape 3 5 0),
  (shape 4 0 4),
  (shape 4 4 0),
  (shape 5 0 3),
  (shape 5 3 0),
  (shape 6 0 2),
  (shape 6 2 0),
  (shape 7 0 1),
  (shape 7 1 0),
  (shape 8 0 0)] := by decide +kernel

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Weights2
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
lemma w50_sound : w50.Encloses (weight (-36170) : ℝ) := by
  exact weight_enclosed_of_trace (-36170) w50Trace w50S0 w50S1 w50S2 w50S3 w50S4 w50S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitB1_1_6
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
lemma Z0_6_2E_2_5Log_sound : Z0_6_2E_2_5Log.Encloses (Real.log (Z0_6_2Value ((2,5) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z0_6_2Probs_sound ((2,5) : PairSlot)) (w := Z0_6_2E_2_5LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z0_6_2E_2_5_sound : Z0_6_2E_2_5.Encloses (Foundation.entropyTerm (Z0_6_2Value ((2,5) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z0_6_2Probs_sound ((2,5) : PairSlot)) Z0_6_2E_2_5Log_sound) (by decide +kernel)
lemma Z0_6_2E_3_5Log_sound : Z0_6_2E_3_5Log.Encloses (Real.log (Z0_6_2Value ((3,5) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z0_6_2Probs_sound ((3,5) : PairSlot)) (w := Z0_6_2E_3_5LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z0_6_2E_3_5_sound : Z0_6_2E_3_5.Encloses (Foundation.entropyTerm (Z0_6_2Value ((3,5) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z0_6_2Probs_sound ((3,5) : PairSlot)) Z0_6_2E_3_5Log_sound) (by decide +kernel)
lemma Z0_6_2E_4_4Log_sound : Z0_6_2E_4_4Log.Encloses (Real.log (Z0_6_2Value ((4,4) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z0_6_2Probs_sound ((4,4) : PairSlot)) (w := Z0_6_2E_4_4LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z0_6_2E_4_4_sound : Z0_6_2E_4_4.Encloses (Foundation.entropyTerm (Z0_6_2Value ((4,4) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z0_6_2Probs_sound ((4,4) : PairSlot)) Z0_6_2E_4_4Log_sound) (by decide +kernel)
lemma Z0_6_2E_5_2Log_sound : Z0_6_2E_5_2Log.Encloses (Real.log (Z0_6_2Value ((5,2) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z0_6_2Probs_sound ((5,2) : PairSlot)) (w := Z0_6_2E_5_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z0_6_2E_5_2_sound : Z0_6_2E_5_2.Encloses (Foundation.entropyTerm (Z0_6_2Value ((5,2) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z0_6_2Probs_sound ((5,2) : PairSlot)) Z0_6_2E_5_2Log_sound) (by decide +kernel)
lemma Z0_6_2E_5_3Log_sound : Z0_6_2E_5_3Log.Encloses (Real.log (Z0_6_2Value ((5,3) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z0_6_2Probs_sound ((5,3) : PairSlot)) (w := Z0_6_2E_5_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z0_6_2E_5_3_sound : Z0_6_2E_5_3.Encloses (Foundation.entropyTerm (Z0_6_2Value ((5,3) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z0_6_2Probs_sound ((5,3) : PairSlot)) Z0_6_2E_5_3Log_sound) (by decide +kernel)
lemma Z0_6_2Terms_sound (a : PairSlot) :
    (Z0_6_2Terms a).Encloses (Foundation.entropyTerm (Z0_6_2Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (entropyTerm_zero_ball (Z0_6_2Probs_sound ((0,0) : PairSlot))) (entropyTerm_zero_ball (Z0_6_2Probs_sound ((0,1) : PairSlot))) (entropyTerm_zero_ball (Z0_6_2Probs_sound ((0,2) : PairSlot))) (entropyTerm_zero_ball (Z0_6_2Probs_sound ((0,3) : PairSlot))) (entropyTerm_zero_ball (Z0_6_2Probs_sound ((0,4) : PairSlot))) (entropyTerm_zero_ball (Z0_6_2Probs_sound ((0,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z0_6_2Probs_sound ((1,0) : PairSlot))) (entropyTerm_zero_ball (Z0_6_2Probs_sound ((1,1) : PairSlot))) (entropyTerm_zero_ball (Z0_6_2Probs_sound ((1,2) : PairSlot))) (entropyTerm_zero_ball (Z0_6_2Probs_sound ((1,3) : PairSlot))) (entropyTerm_zero_ball (Z0_6_2Probs_sound ((1,4) : PairSlot))) (entropyTerm_zero_ball (Z0_6_2Probs_sound ((1,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z0_6_2Probs_sound ((2,0) : PairSlot))) (entropyTerm_zero_ball (Z0_6_2Probs_sound ((2,1) : PairSlot))) (entropyTerm_zero_ball (Z0_6_2Probs_sound ((2,2) : PairSlot))) (entropyTerm_zero_ball (Z0_6_2Probs_sound ((2,3) : PairSlot))) (entropyTerm_zero_ball (Z0_6_2Probs_sound ((2,4) : PairSlot))) Z0_6_2E_2_5_sound
  · exact forall_fin6 (entropyTerm_zero_ball (Z0_6_2Probs_sound ((3,0) : PairSlot))) (entropyTerm_zero_ball (Z0_6_2Probs_sound ((3,1) : PairSlot))) (entropyTerm_zero_ball (Z0_6_2Probs_sound ((3,2) : PairSlot))) (entropyTerm_zero_ball (Z0_6_2Probs_sound ((3,3) : PairSlot))) (entropyTerm_zero_ball (Z0_6_2Probs_sound ((3,4) : PairSlot))) Z0_6_2E_3_5_sound
  · exact forall_fin6 (entropyTerm_zero_ball (Z0_6_2Probs_sound ((4,0) : PairSlot))) (entropyTerm_zero_ball (Z0_6_2Probs_sound ((4,1) : PairSlot))) (entropyTerm_zero_ball (Z0_6_2Probs_sound ((4,2) : PairSlot))) (entropyTerm_zero_ball (Z0_6_2Probs_sound ((4,3) : PairSlot))) Z0_6_2E_4_4_sound (entropyTerm_zero_ball (Z0_6_2Probs_sound ((4,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z0_6_2Probs_sound ((5,0) : PairSlot))) (entropyTerm_zero_ball (Z0_6_2Probs_sound ((5,1) : PairSlot))) Z0_6_2E_5_2_sound Z0_6_2E_5_3_sound (entropyTerm_zero_ball (Z0_6_2Probs_sound ((5,4) : PairSlot))) (entropyTerm_zero_ball (Z0_6_2Probs_sound ((5,5) : PairSlot)))
lemma Z0_6_2Entropy_sound : Z0_6_2Entropy.Encloses (Foundation.finiteEntropy Z0_6_2Value) := by
  exact contains_sound (entropyPair_enclosed Z0_6_2Value Z0_6_2Terms Z0_6_2Terms_sound) (by decide +kernel)
lemma Z0_6_2Labels_sound : Z0_6_2Labels.Encloses
    (∑ a : PairSlot, (zeroPairLaw (shape 0 6 2) a.1 a.2 : ℝ) *
      Real.log (AllFieldParameters.multiplicity a.1 * AllFieldParameters.multiplicity a.2 : ℕ)) := by
  exact contains_sound (pairSumBall_sound (fun a => .mul (Z0_6_2Probs a) (multLogs a))
    _ (fun a => Ball.mul_sound (Z0_6_2Probs_sound a) (multLogs_sound a))) (by decide +kernel)
lemma Z0_6_2Four_sound : Z0_6_2Four.Encloses (AllFieldZeroLeafRates.fourRate (shape 0 6 2)) := by
  exact contains_sound (Ball.add_sound Z0_6_2Entropy_sound Z0_6_2Labels_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitA1_3_12
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
open AllFieldInitialEntropyCertificate
open scoped BigOperators
lemma w125_sound : w125.Encloses (weight (-11037) : ℝ) := by
  exact weight_enclosed_of_trace (-11037) w125Trace w125S0 w125S1 w125S2 w125S3 w125S4 w125S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
lemma Z0_2_6Raw_sound_0 (j : Fin 6) :
    (Z0_2_6Raw (0,j)).Encloses (weight (orderedPairInteger (shape 0 2 6) 0 j) : ℝ) := by
  fin_cases j
  · change (Z0_2_6Raw (0,0)).Encloses (weight (orderedPairInteger (shape 0 2 6) 0 0) : ℝ)
    have he : orderedPairInteger (shape 0 2 6) 0 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_2_6Raw (0,1)).Encloses (weight (orderedPairInteger (shape 0 2 6) 0 1) : ℝ)
    have he : orderedPairInteger (shape 0 2 6) 0 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_2_6Raw (0,2)).Encloses (weight (orderedPairInteger (shape 0 2 6) 0 2) : ℝ)
    have he : orderedPairInteger (shape 0 2 6) 0 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_2_6Raw (0,3)).Encloses (weight (orderedPairInteger (shape 0 2 6) 0 3) : ℝ)
    have he : orderedPairInteger (shape 0 2 6) 0 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_2_6Raw (0,4)).Encloses (weight (orderedPairInteger (shape 0 2 6) 0 4) : ℝ)
    have he : orderedPairInteger (shape 0 2 6) 0 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_2_6Raw (0,5)).Encloses (weight (orderedPairInteger (shape 0 2 6) 0 5) : ℝ)
    have he : orderedPairInteger (shape 0 2 6) 0 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_2_6Raw_sound_1 (j : Fin 6) :
    (Z0_2_6Raw (1,j)).Encloses (weight (orderedPairInteger (shape 0 2 6) 1 j) : ℝ) := by
  fin_cases j
  · change (Z0_2_6Raw (1,0)).Encloses (weight (orderedPairInteger (shape 0 2 6) 1 0) : ℝ)
    have he : orderedPairInteger (shape 0 2 6) 1 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_2_6Raw (1,1)).Encloses (weight (orderedPairInteger (shape 0 2 6) 1 1) : ℝ)
    have he : orderedPairInteger (shape 0 2 6) 1 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_2_6Raw (1,2)).Encloses (weight (orderedPairInteger (shape 0 2 6) 1 2) : ℝ)
    have he : orderedPairInteger (shape 0 2 6) 1 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_2_6Raw (1,3)).Encloses (weight (orderedPairInteger (shape 0 2 6) 1 3) : ℝ)
    have he : orderedPairInteger (shape 0 2 6) 1 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_2_6Raw (1,4)).Encloses (weight (orderedPairInteger (shape 0 2 6) 1 4) : ℝ)
    have he : orderedPairInteger (shape 0 2 6) 1 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_2_6Raw (1,5)).Encloses (weight (orderedPairInteger (shape 0 2 6) 1 5) : ℝ)
    have he : orderedPairInteger (shape 0 2 6) 1 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_2_6Raw_sound_2 (j : Fin 6) :
    (Z0_2_6Raw (2,j)).Encloses (weight (orderedPairInteger (shape 0 2 6) 2 j) : ℝ) := by
  fin_cases j
  · change (Z0_2_6Raw (2,0)).Encloses (weight (orderedPairInteger (shape 0 2 6) 2 0) : ℝ)
    have he : orderedPairInteger (shape 0 2 6) 2 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_2_6Raw (2,1)).Encloses (weight (orderedPairInteger (shape 0 2 6) 2 1) : ℝ)
    have he : orderedPairInteger (shape 0 2 6) 2 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_2_6Raw (2,2)).Encloses (weight (orderedPairInteger (shape 0 2 6) 2 2) : ℝ)
    have he : orderedPairInteger (shape 0 2 6) 2 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_2_6Raw (2,3)).Encloses (weight (orderedPairInteger (shape 0 2 6) 2 3) : ℝ)
    have he : orderedPairInteger (shape 0 2 6) 2 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_2_6Raw (2,4)).Encloses (weight (orderedPairInteger (shape 0 2 6) 2 4) : ℝ)
    have he : orderedPairInteger (shape 0 2 6) 2 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_2_6Raw (2,5)).Encloses (weight (orderedPairInteger (shape 0 2 6) 2 5) : ℝ)
    have he : orderedPairInteger (shape 0 2 6) 2 5 = (-11037) := by decide +kernel
    rw [he]
    exact w125_sound
lemma Z0_2_6Raw_sound_3 (j : Fin 6) :
    (Z0_2_6Raw (3,j)).Encloses (weight (orderedPairInteger (shape 0 2 6) 3 j) : ℝ) := by
  fin_cases j
  · change (Z0_2_6Raw (3,0)).Encloses (weight (orderedPairInteger (shape 0 2 6) 3 0) : ℝ)
    have he : orderedPairInteger (shape 0 2 6) 3 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_2_6Raw (3,1)).Encloses (weight (orderedPairInteger (shape 0 2 6) 3 1) : ℝ)
    have he : orderedPairInteger (shape 0 2 6) 3 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_2_6Raw (3,2)).Encloses (weight (orderedPairInteger (shape 0 2 6) 3 2) : ℝ)
    have he : orderedPairInteger (shape 0 2 6) 3 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_2_6Raw (3,3)).Encloses (weight (orderedPairInteger (shape 0 2 6) 3 3) : ℝ)
    have he : orderedPairInteger (shape 0 2 6) 3 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_2_6Raw (3,4)).Encloses (weight (orderedPairInteger (shape 0 2 6) 3 4) : ℝ)
    have he : orderedPairInteger (shape 0 2 6) 3 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_2_6Raw (3,5)).Encloses (weight (orderedPairInteger (shape 0 2 6) 3 5) : ℝ)
    have he : orderedPairInteger (shape 0 2 6) 3 5 = (-36170) := by decide +kernel
    rw [he]
    exact w50_sound
lemma Z0_2_6Raw_sound_4 (j : Fin 6) :
    (Z0_2_6Raw (4,j)).Encloses (weight (orderedPairInteger (shape 0 2 6) 4 j) : ℝ) := by
  fin_cases j
  · change (Z0_2_6Raw (4,0)).Encloses (weight (orderedPairInteger (shape 0 2 6) 4 0) : ℝ)
    have he : orderedPairInteger (shape 0 2 6) 4 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_2_6Raw (4,1)).Encloses (weight (orderedPairInteger (shape 0 2 6) 4 1) : ℝ)
    have he : orderedPairInteger (shape 0 2 6) 4 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_2_6Raw (4,2)).Encloses (weight (orderedPairInteger (shape 0 2 6) 4 2) : ℝ)
    have he : orderedPairInteger (shape 0 2 6) 4 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_2_6Raw (4,3)).Encloses (weight (orderedPairInteger (shape 0 2 6) 4 3) : ℝ)
    have he : orderedPairInteger (shape 0 2 6) 4 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_2_6Raw (4,4)).Encloses (weight (orderedPairInteger (shape 0 2 6) 4 4) : ℝ)
    have he : orderedPairInteger (shape 0 2 6) 4 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_2_6Raw (4,5)).Encloses (weight (orderedPairInteger (shape 0 2 6) 4 5) : ℝ)
    have he : orderedPairInteger (shape 0 2 6) 4 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_2_6Raw_sound_5 (j : Fin 6) :
    (Z0_2_6Raw (5,j)).Encloses (weight (orderedPairInteger (shape 0 2 6) 5 j) : ℝ) := by
  fin_cases j
  · change (Z0_2_6Raw (5,0)).Encloses (weight (orderedPairInteger (shape 0 2 6) 5 0) : ℝ)
    have he : orderedPairInteger (shape 0 2 6) 5 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_2_6Raw (5,1)).Encloses (weight (orderedPairInteger (shape 0 2 6) 5 1) : ℝ)
    have he : orderedPairInteger (shape 0 2 6) 5 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_2_6Raw (5,2)).Encloses (weight (orderedPairInteger (shape 0 2 6) 5 2) : ℝ)
    have he : orderedPairInteger (shape 0 2 6) 5 2 = (-11037) := by decide +kernel
    rw [he]
    exact w125_sound
  · change (Z0_2_6Raw (5,3)).Encloses (weight (orderedPairInteger (shape 0 2 6) 5 3) : ℝ)
    have he : orderedPairInteger (shape 0 2 6) 5 3 = (-36170) := by decide +kernel
    rw [he]
    exact w50_sound
  · change (Z0_2_6Raw (5,4)).Encloses (weight (orderedPairInteger (shape 0 2 6) 5 4) : ℝ)
    have he : orderedPairInteger (shape 0 2 6) 5 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_2_6Raw (5,5)).Encloses (weight (orderedPairInteger (shape 0 2 6) 5 5) : ℝ)
    have he : orderedPairInteger (shape 0 2 6) 5 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_2_6Raw_sound (ij : PairSlot) :
    (Z0_2_6Raw ij).Encloses (weight (orderedPairInteger (shape 0 2 6) ij.1 ij.2) : ℝ) := by
  rcases ij with ⟨i,j⟩
  revert i
  exact forall_fin6 (Z0_2_6Raw_sound_0 j) (Z0_2_6Raw_sound_1 j) (Z0_2_6Raw_sound_2 j) (Z0_2_6Raw_sound_3 j) (Z0_2_6Raw_sound_4 j) (Z0_2_6Raw_sound_5 j)
lemma Z0_2_6Den_sound : Z0_2_6Den.Encloses
    (((orderedPairs (shape 0 2 6)).map (fun ij => weight (orderedPairInteger (shape 0 2 6) ij.1 ij.2))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (orderedPairs (shape 0 2 6)) Z0_2_6Raw
    (fun ij => weight (orderedPairInteger (shape 0 2 6) ij.1 ij.2))
    (fun ij _ => Z0_2_6Raw_sound ij)) (by decide +kernel)
lemma Z0_2_6Den_pos : 0 < Z0_2_6Den.lower := by decide +kernel
lemma Z0_2_6Contains : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j = shapeMax (shape 0 2 6) →
    contains (.mul (Z0_2_6Raw (i,j)) (.inv Z0_2_6Den)) (Z0_2_6Probs (i,j)) = true := by
  decide +kernel
lemma Z0_2_6Zero : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j ≠ shapeMax (shape 0 2 6) → Z0_2_6Probs (i,j) = .exact 0 := by
  decide +kernel
lemma Z0_2_6Probs_sound (ij : PairSlot) :
    (Z0_2_6Probs ij).Encloses (zeroPairLaw (shape 0 2 6) ij.1 ij.2 : ℝ) := by
  by_cases h : statisticWeight ij.1 + statisticWeight ij.2 = shapeMax (shape 0 2 6)
  · have hb := contains_sound (Ball.mul_sound (Z0_2_6Raw_sound ij)
      (Ball.inv_sound Z0_2_6Den_sound Z0_2_6Den_pos)) (Z0_2_6Contains ij.1 ij.2 h)
    simpa only [zeroPairLaw, h, ite_true, if_true, Rat.cast_div, Rat.cast_mul,
      Rat.cast_inv, div_eq_mul_inv] using hb
  · rw [Z0_2_6Zero ij.1 ij.2 h]
    simpa only [zeroPairLaw, h, ite_false, if_false] using Ball.exact_sound 0

lemma Z0_2_6E_2_5Log_sound : Z0_2_6E_2_5Log.Encloses (Real.log (Z0_2_6Value ((2,5) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z0_2_6Probs_sound ((2,5) : PairSlot)) (w := Z0_2_6E_2_5LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z0_2_6E_2_5_sound : Z0_2_6E_2_5.Encloses (Foundation.entropyTerm (Z0_2_6Value ((2,5) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z0_2_6Probs_sound ((2,5) : PairSlot)) Z0_2_6E_2_5Log_sound) (by decide +kernel)
lemma Z0_2_6E_3_5Log_sound : Z0_2_6E_3_5Log.Encloses (Real.log (Z0_2_6Value ((3,5) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z0_2_6Probs_sound ((3,5) : PairSlot)) (w := Z0_2_6E_3_5LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z0_2_6E_3_5_sound : Z0_2_6E_3_5.Encloses (Foundation.entropyTerm (Z0_2_6Value ((3,5) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z0_2_6Probs_sound ((3,5) : PairSlot)) Z0_2_6E_3_5Log_sound) (by decide +kernel)
lemma Z0_2_6E_4_4Log_sound : Z0_2_6E_4_4Log.Encloses (Real.log (Z0_2_6Value ((4,4) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z0_2_6Probs_sound ((4,4) : PairSlot)) (w := Z0_2_6E_4_4LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z0_2_6E_4_4_sound : Z0_2_6E_4_4.Encloses (Foundation.entropyTerm (Z0_2_6Value ((4,4) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z0_2_6Probs_sound ((4,4) : PairSlot)) Z0_2_6E_4_4Log_sound) (by decide +kernel)
lemma Z0_2_6E_5_2Log_sound : Z0_2_6E_5_2Log.Encloses (Real.log (Z0_2_6Value ((5,2) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z0_2_6Probs_sound ((5,2) : PairSlot)) (w := Z0_2_6E_5_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z0_2_6E_5_2_sound : Z0_2_6E_5_2.Encloses (Foundation.entropyTerm (Z0_2_6Value ((5,2) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z0_2_6Probs_sound ((5,2) : PairSlot)) Z0_2_6E_5_2Log_sound) (by decide +kernel)
lemma Z0_2_6E_5_3Log_sound : Z0_2_6E_5_3Log.Encloses (Real.log (Z0_2_6Value ((5,3) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z0_2_6Probs_sound ((5,3) : PairSlot)) (w := Z0_2_6E_5_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z0_2_6E_5_3_sound : Z0_2_6E_5_3.Encloses (Foundation.entropyTerm (Z0_2_6Value ((5,3) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z0_2_6Probs_sound ((5,3) : PairSlot)) Z0_2_6E_5_3Log_sound) (by decide +kernel)
lemma Z0_2_6Terms_sound (a : PairSlot) :
    (Z0_2_6Terms a).Encloses (Foundation.entropyTerm (Z0_2_6Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (entropyTerm_zero_ball (Z0_2_6Probs_sound ((0,0) : PairSlot))) (entropyTerm_zero_ball (Z0_2_6Probs_sound ((0,1) : PairSlot))) (entropyTerm_zero_ball (Z0_2_6Probs_sound ((0,2) : PairSlot))) (entropyTerm_zero_ball (Z0_2_6Probs_sound ((0,3) : PairSlot))) (entropyTerm_zero_ball (Z0_2_6Probs_sound ((0,4) : PairSlot))) (entropyTerm_zero_ball (Z0_2_6Probs_sound ((0,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z0_2_6Probs_sound ((1,0) : PairSlot))) (entropyTerm_zero_ball (Z0_2_6Probs_sound ((1,1) : PairSlot))) (entropyTerm_zero_ball (Z0_2_6Probs_sound ((1,2) : PairSlot))) (entropyTerm_zero_ball (Z0_2_6Probs_sound ((1,3) : PairSlot))) (entropyTerm_zero_ball (Z0_2_6Probs_sound ((1,4) : PairSlot))) (entropyTerm_zero_ball (Z0_2_6Probs_sound ((1,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z0_2_6Probs_sound ((2,0) : PairSlot))) (entropyTerm_zero_ball (Z0_2_6Probs_sound ((2,1) : PairSlot))) (entropyTerm_zero_ball (Z0_2_6Probs_sound ((2,2) : PairSlot))) (entropyTerm_zero_ball (Z0_2_6Probs_sound ((2,3) : PairSlot))) (entropyTerm_zero_ball (Z0_2_6Probs_sound ((2,4) : PairSlot))) Z0_2_6E_2_5_sound
  · exact forall_fin6 (entropyTerm_zero_ball (Z0_2_6Probs_sound ((3,0) : PairSlot))) (entropyTerm_zero_ball (Z0_2_6Probs_sound ((3,1) : PairSlot))) (entropyTerm_zero_ball (Z0_2_6Probs_sound ((3,2) : PairSlot))) (entropyTerm_zero_ball (Z0_2_6Probs_sound ((3,3) : PairSlot))) (entropyTerm_zero_ball (Z0_2_6Probs_sound ((3,4) : PairSlot))) Z0_2_6E_3_5_sound
  · exact forall_fin6 (entropyTerm_zero_ball (Z0_2_6Probs_sound ((4,0) : PairSlot))) (entropyTerm_zero_ball (Z0_2_6Probs_sound ((4,1) : PairSlot))) (entropyTerm_zero_ball (Z0_2_6Probs_sound ((4,2) : PairSlot))) (entropyTerm_zero_ball (Z0_2_6Probs_sound ((4,3) : PairSlot))) Z0_2_6E_4_4_sound (entropyTerm_zero_ball (Z0_2_6Probs_sound ((4,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z0_2_6Probs_sound ((5,0) : PairSlot))) (entropyTerm_zero_ball (Z0_2_6Probs_sound ((5,1) : PairSlot))) Z0_2_6E_5_2_sound Z0_2_6E_5_3_sound (entropyTerm_zero_ball (Z0_2_6Probs_sound ((5,4) : PairSlot))) (entropyTerm_zero_ball (Z0_2_6Probs_sound ((5,5) : PairSlot)))
lemma Z0_2_6Entropy_sound : Z0_2_6Entropy.Encloses (Foundation.finiteEntropy Z0_2_6Value) := by
  exact contains_sound (entropyPair_enclosed Z0_2_6Value Z0_2_6Terms Z0_2_6Terms_sound) (by decide +kernel)
lemma Z0_2_6Labels_sound : Z0_2_6Labels.Encloses
    (∑ a : PairSlot, (zeroPairLaw (shape 0 2 6) a.1 a.2 : ℝ) *
      Real.log (AllFieldParameters.multiplicity a.1 * AllFieldParameters.multiplicity a.2 : ℕ)) := by
  exact contains_sound (pairSumBall_sound (fun a => .mul (Z0_2_6Probs a) (multLogs a))
    _ (fun a => Ball.mul_sound (Z0_2_6Probs_sound a) (multLogs_sound a))) (by decide +kernel)
lemma Z0_2_6Four_sound : Z0_2_6Four.Encloses (AllFieldZeroLeafRates.fourRate (shape 0 2 6)) := by
  exact contains_sound (Ball.add_sound Z0_2_6Entropy_sound Z0_2_6Labels_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

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
lemma fourRateBalls_sound_oai (t : Shape) (ht : t ∈ zeroSecond) :
    (fourRateBalls t).Encloses (AllFieldZeroLeafRates.fourRate t) := by
  rw [zeroSecond_list] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Z0_0_8Four_sound
  · exact Z0_1_7Four_sound
  · exact Z0_2_6Four_sound
  · exact Z0_3_5Four_sound
  · exact Z0_4_4Four_sound
  · exact Z0_5_3Four_sound
  · exact Z0_6_2Four_sound
  · exact Z0_7_1Four_sound
  · exact Z0_8_0Four_sound
  · exact Z1_0_7Four_sound
  · exact Z1_7_0Four_sound
  · exact Z2_0_6Four_sound
  · exact Z2_6_0Four_sound
  · exact Z3_0_5Four_sound
  · exact Z3_5_0Four_sound
  · exact Z4_0_4Four_sound
  · exact Z4_4_0Four_sound
  · exact Z5_0_3Four_sound
  · exact Z5_3_0Four_sound
  · exact Z6_0_2Four_sound
  · exact Z6_2_0Four_sound
  · exact Z7_0_1Four_sound
  · exact Z7_1_0Four_sound
  · exact Z8_0_0Four_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.fourRateBalls_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.fourRateBalls_sound_oai
