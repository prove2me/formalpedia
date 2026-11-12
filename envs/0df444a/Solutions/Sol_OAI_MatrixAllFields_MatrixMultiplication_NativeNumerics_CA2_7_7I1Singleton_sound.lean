-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_7_7I1Singleton_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T14:03:38.260621+00:00
-- url     : https://prove2.me/submissions/8d034718-1793-484a-b473-32c09f5d5806

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
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_A2_7_7Law_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_entropyTerm_ball
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_homogeneous_enclosed

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

lemma singletonBall_sound {A : Type*} [Fintype A] (support : List Shape)
    (bs : Shape → Ball) (p : Shape → ℝ) (priority : Placement) (position : Fin 3)
    (be : Shape → Ball) (q : Shape → A → ℝ)
    (hp : ∀ u ∈ support, (bs u).Encloses (p u))
    (he : ∀ u ∈ support, designated priority position u →
      (be u).Encloses (homogeneousEntropy (q u))) :
    (singletonBall support bs priority position be).Encloses
      (singletonEntropy support p priority position q) := by
  apply listSumBall_sound
  intro u hu
  by_cases hk : designated priority position u
  · simpa only [hk, ite_true, if_true] using Ball.mul_sound (hp u hu) (he u hu hk)
  · simpa only [hk, ite_false, if_false, Rat.cast_zero] using Ball.exact_sound 0

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
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Four0_4_4
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
lemma w122_sound : w122.Encloses (weight (-12708) : ℝ) := by
  exact weight_enclosed_of_trace (-12708) w122Trace w122S0 w122S1 w122S2 w122S3 w122S4 w122S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitB1_1_6
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
lemma w49_sound : w49.Encloses (weight (-36610) : ℝ) := by
  exact weight_enclosed_of_trace (-36610) w49Trace w49S0 w49S1 w49S2 w49S3 w49S4 w49S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Four1_7_0
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
lemma Z1_7_0Raw_sound_0 (j : Fin 6) :
    (Z1_7_0Raw (0,j)).Encloses (weight (orderedPairInteger (shape 1 7 0) 0 j) : ℝ) := by
  fin_cases j
  · change (Z1_7_0Raw (0,0)).Encloses (weight (orderedPairInteger (shape 1 7 0) 0 0) : ℝ)
    have he : orderedPairInteger (shape 1 7 0) 0 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_7_0Raw (0,1)).Encloses (weight (orderedPairInteger (shape 1 7 0) 0 1) : ℝ)
    have he : orderedPairInteger (shape 1 7 0) 0 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_7_0Raw (0,2)).Encloses (weight (orderedPairInteger (shape 1 7 0) 0 2) : ℝ)
    have he : orderedPairInteger (shape 1 7 0) 0 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_7_0Raw (0,3)).Encloses (weight (orderedPairInteger (shape 1 7 0) 0 3) : ℝ)
    have he : orderedPairInteger (shape 1 7 0) 0 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_7_0Raw (0,4)).Encloses (weight (orderedPairInteger (shape 1 7 0) 0 4) : ℝ)
    have he : orderedPairInteger (shape 1 7 0) 0 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_7_0Raw (0,5)).Encloses (weight (orderedPairInteger (shape 1 7 0) 0 5) : ℝ)
    have he : orderedPairInteger (shape 1 7 0) 0 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z1_7_0Raw_sound_1 (j : Fin 6) :
    (Z1_7_0Raw (1,j)).Encloses (weight (orderedPairInteger (shape 1 7 0) 1 j) : ℝ) := by
  fin_cases j
  · change (Z1_7_0Raw (1,0)).Encloses (weight (orderedPairInteger (shape 1 7 0) 1 0) : ℝ)
    have he : orderedPairInteger (shape 1 7 0) 1 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_7_0Raw (1,1)).Encloses (weight (orderedPairInteger (shape 1 7 0) 1 1) : ℝ)
    have he : orderedPairInteger (shape 1 7 0) 1 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_7_0Raw (1,2)).Encloses (weight (orderedPairInteger (shape 1 7 0) 1 2) : ℝ)
    have he : orderedPairInteger (shape 1 7 0) 1 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_7_0Raw (1,3)).Encloses (weight (orderedPairInteger (shape 1 7 0) 1 3) : ℝ)
    have he : orderedPairInteger (shape 1 7 0) 1 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_7_0Raw (1,4)).Encloses (weight (orderedPairInteger (shape 1 7 0) 1 4) : ℝ)
    have he : orderedPairInteger (shape 1 7 0) 1 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_7_0Raw (1,5)).Encloses (weight (orderedPairInteger (shape 1 7 0) 1 5) : ℝ)
    have he : orderedPairInteger (shape 1 7 0) 1 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z1_7_0Raw_sound_2 (j : Fin 6) :
    (Z1_7_0Raw (2,j)).Encloses (weight (orderedPairInteger (shape 1 7 0) 2 j) : ℝ) := by
  fin_cases j
  · change (Z1_7_0Raw (2,0)).Encloses (weight (orderedPairInteger (shape 1 7 0) 2 0) : ℝ)
    have he : orderedPairInteger (shape 1 7 0) 2 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_7_0Raw (2,1)).Encloses (weight (orderedPairInteger (shape 1 7 0) 2 1) : ℝ)
    have he : orderedPairInteger (shape 1 7 0) 2 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_7_0Raw (2,2)).Encloses (weight (orderedPairInteger (shape 1 7 0) 2 2) : ℝ)
    have he : orderedPairInteger (shape 1 7 0) 2 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_7_0Raw (2,3)).Encloses (weight (orderedPairInteger (shape 1 7 0) 2 3) : ℝ)
    have he : orderedPairInteger (shape 1 7 0) 2 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_7_0Raw (2,4)).Encloses (weight (orderedPairInteger (shape 1 7 0) 2 4) : ℝ)
    have he : orderedPairInteger (shape 1 7 0) 2 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_7_0Raw (2,5)).Encloses (weight (orderedPairInteger (shape 1 7 0) 2 5) : ℝ)
    have he : orderedPairInteger (shape 1 7 0) 2 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z1_7_0Raw_sound_3 (j : Fin 6) :
    (Z1_7_0Raw (3,j)).Encloses (weight (orderedPairInteger (shape 1 7 0) 3 j) : ℝ) := by
  fin_cases j
  · change (Z1_7_0Raw (3,0)).Encloses (weight (orderedPairInteger (shape 1 7 0) 3 0) : ℝ)
    have he : orderedPairInteger (shape 1 7 0) 3 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_7_0Raw (3,1)).Encloses (weight (orderedPairInteger (shape 1 7 0) 3 1) : ℝ)
    have he : orderedPairInteger (shape 1 7 0) 3 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_7_0Raw (3,2)).Encloses (weight (orderedPairInteger (shape 1 7 0) 3 2) : ℝ)
    have he : orderedPairInteger (shape 1 7 0) 3 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_7_0Raw (3,3)).Encloses (weight (orderedPairInteger (shape 1 7 0) 3 3) : ℝ)
    have he : orderedPairInteger (shape 1 7 0) 3 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_7_0Raw (3,4)).Encloses (weight (orderedPairInteger (shape 1 7 0) 3 4) : ℝ)
    have he : orderedPairInteger (shape 1 7 0) 3 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_7_0Raw (3,5)).Encloses (weight (orderedPairInteger (shape 1 7 0) 3 5) : ℝ)
    have he : orderedPairInteger (shape 1 7 0) 3 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z1_7_0Raw_sound_4 (j : Fin 6) :
    (Z1_7_0Raw (4,j)).Encloses (weight (orderedPairInteger (shape 1 7 0) 4 j) : ℝ) := by
  fin_cases j
  · change (Z1_7_0Raw (4,0)).Encloses (weight (orderedPairInteger (shape 1 7 0) 4 0) : ℝ)
    have he : orderedPairInteger (shape 1 7 0) 4 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_7_0Raw (4,1)).Encloses (weight (orderedPairInteger (shape 1 7 0) 4 1) : ℝ)
    have he : orderedPairInteger (shape 1 7 0) 4 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_7_0Raw (4,2)).Encloses (weight (orderedPairInteger (shape 1 7 0) 4 2) : ℝ)
    have he : orderedPairInteger (shape 1 7 0) 4 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_7_0Raw (4,3)).Encloses (weight (orderedPairInteger (shape 1 7 0) 4 3) : ℝ)
    have he : orderedPairInteger (shape 1 7 0) 4 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_7_0Raw (4,4)).Encloses (weight (orderedPairInteger (shape 1 7 0) 4 4) : ℝ)
    have he : orderedPairInteger (shape 1 7 0) 4 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_7_0Raw (4,5)).Encloses (weight (orderedPairInteger (shape 1 7 0) 4 5) : ℝ)
    have he : orderedPairInteger (shape 1 7 0) 4 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z1_7_0Raw_sound_5 (j : Fin 6) :
    (Z1_7_0Raw (5,j)).Encloses (weight (orderedPairInteger (shape 1 7 0) 5 j) : ℝ) := by
  fin_cases j
  · change (Z1_7_0Raw (5,0)).Encloses (weight (orderedPairInteger (shape 1 7 0) 5 0) : ℝ)
    have he : orderedPairInteger (shape 1 7 0) 5 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_7_0Raw (5,1)).Encloses (weight (orderedPairInteger (shape 1 7 0) 5 1) : ℝ)
    have he : orderedPairInteger (shape 1 7 0) 5 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_7_0Raw (5,2)).Encloses (weight (orderedPairInteger (shape 1 7 0) 5 2) : ℝ)
    have he : orderedPairInteger (shape 1 7 0) 5 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_7_0Raw (5,3)).Encloses (weight (orderedPairInteger (shape 1 7 0) 5 3) : ℝ)
    have he : orderedPairInteger (shape 1 7 0) 5 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_7_0Raw (5,4)).Encloses (weight (orderedPairInteger (shape 1 7 0) 5 4) : ℝ)
    have he : orderedPairInteger (shape 1 7 0) 5 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z1_7_0Raw (5,5)).Encloses (weight (orderedPairInteger (shape 1 7 0) 5 5) : ℝ)
    have he : orderedPairInteger (shape 1 7 0) 5 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z1_7_0Raw_sound (ij : PairSlot) :
    (Z1_7_0Raw ij).Encloses (weight (orderedPairInteger (shape 1 7 0) ij.1 ij.2) : ℝ) := by
  rcases ij with ⟨i,j⟩
  revert i
  exact forall_fin6 (Z1_7_0Raw_sound_0 j) (Z1_7_0Raw_sound_1 j) (Z1_7_0Raw_sound_2 j) (Z1_7_0Raw_sound_3 j) (Z1_7_0Raw_sound_4 j) (Z1_7_0Raw_sound_5 j)
lemma Z1_7_0Den_sound : Z1_7_0Den.Encloses
    (((orderedPairs (shape 1 7 0)).map (fun ij => weight (orderedPairInteger (shape 1 7 0) ij.1 ij.2))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (orderedPairs (shape 1 7 0)) Z1_7_0Raw
    (fun ij => weight (orderedPairInteger (shape 1 7 0) ij.1 ij.2))
    (fun ij _ => Z1_7_0Raw_sound ij)) (by decide +kernel)
lemma Z1_7_0Den_pos : 0 < Z1_7_0Den.lower := by decide +kernel
lemma Z1_7_0Contains : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j = shapeMax (shape 1 7 0) →
    contains (.mul (Z1_7_0Raw (i,j)) (.inv Z1_7_0Den)) (Z1_7_0Probs (i,j)) = true := by
  decide +kernel
lemma Z1_7_0Zero : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j ≠ shapeMax (shape 1 7 0) → Z1_7_0Probs (i,j) = .exact 0 := by
  decide +kernel
lemma Z1_7_0Probs_sound (ij : PairSlot) :
    (Z1_7_0Probs ij).Encloses (zeroPairLaw (shape 1 7 0) ij.1 ij.2 : ℝ) := by
  by_cases h : statisticWeight ij.1 + statisticWeight ij.2 = shapeMax (shape 1 7 0)
  · have hb := contains_sound (Ball.mul_sound (Z1_7_0Raw_sound ij)
      (Ball.inv_sound Z1_7_0Den_sound Z1_7_0Den_pos)) (Z1_7_0Contains ij.1 ij.2 h)
    simpa only [zeroPairLaw, h, ite_true, if_true, Rat.cast_div, Rat.cast_mul,
      Rat.cast_inv, div_eq_mul_inv] using hb
  · rw [Z1_7_0Zero ij.1 ij.2 h]
    simpa only [zeroPairLaw, h, ite_false, if_false] using Ball.exact_sound 0

lemma Z1_7_0Half_sound (w : Fin 3) (ij : PairSlot) :
    (Z1_7_0Half w ij).Encloses (halfLaw (shape 1 7 0) w ij : ℝ) := by
  have hp : positive (shape 1 7 0) = false := by decide +kernel
  simp only [Z1_7_0Half, halfLaw, hp, Bool.false_eq_true, ite_false, if_false]
  split_ifs
  · exact Ball.exact_sound 1
  · exact Ball.exact_sound 0
  · exact Z1_7_0Probs_sound _
  · exact Z1_7_0Probs_sound _

lemma Z1_7_0H1E_4_5Log_sound : Z1_7_0H1E_4_5Log.Encloses (Real.log (Z1_7_0H1Value ((4,5) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z1_7_0Half_sound 1) ((4,5) : PairSlot)) (w := Z1_7_0H1E_4_5LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z1_7_0H1E_4_5_sound : Z1_7_0H1E_4_5.Encloses (Foundation.entropyTerm (Z1_7_0H1Value ((4,5) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z1_7_0Half_sound 1) ((4,5) : PairSlot)) Z1_7_0H1E_4_5Log_sound) (by decide +kernel)
lemma Z1_7_0H1E_5_4Log_sound : Z1_7_0H1E_5_4Log.Encloses (Real.log (Z1_7_0H1Value ((5,4) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z1_7_0Half_sound 1) ((5,4) : PairSlot)) (w := Z1_7_0H1E_5_4LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z1_7_0H1E_5_4_sound : Z1_7_0H1E_5_4.Encloses (Foundation.entropyTerm (Z1_7_0H1Value ((5,4) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z1_7_0Half_sound 1) ((5,4) : PairSlot)) Z1_7_0H1E_5_4Log_sound) (by decide +kernel)
lemma Z1_7_0H1Terms_sound (a : PairSlot) :
    (Z1_7_0H1Terms a).Encloses (Foundation.entropyTerm (Z1_7_0H1Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (entropyTerm_zero_ball ((Z1_7_0Half_sound 1) ((0,0) : PairSlot))) (entropyTerm_zero_ball ((Z1_7_0Half_sound 1) ((0,1) : PairSlot))) (entropyTerm_zero_ball ((Z1_7_0Half_sound 1) ((0,2) : PairSlot))) (entropyTerm_zero_ball ((Z1_7_0Half_sound 1) ((0,3) : PairSlot))) (entropyTerm_zero_ball ((Z1_7_0Half_sound 1) ((0,4) : PairSlot))) (entropyTerm_zero_ball ((Z1_7_0Half_sound 1) ((0,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z1_7_0Half_sound 1) ((1,0) : PairSlot))) (entropyTerm_zero_ball ((Z1_7_0Half_sound 1) ((1,1) : PairSlot))) (entropyTerm_zero_ball ((Z1_7_0Half_sound 1) ((1,2) : PairSlot))) (entropyTerm_zero_ball ((Z1_7_0Half_sound 1) ((1,3) : PairSlot))) (entropyTerm_zero_ball ((Z1_7_0Half_sound 1) ((1,4) : PairSlot))) (entropyTerm_zero_ball ((Z1_7_0Half_sound 1) ((1,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z1_7_0Half_sound 1) ((2,0) : PairSlot))) (entropyTerm_zero_ball ((Z1_7_0Half_sound 1) ((2,1) : PairSlot))) (entropyTerm_zero_ball ((Z1_7_0Half_sound 1) ((2,2) : PairSlot))) (entropyTerm_zero_ball ((Z1_7_0Half_sound 1) ((2,3) : PairSlot))) (entropyTerm_zero_ball ((Z1_7_0Half_sound 1) ((2,4) : PairSlot))) (entropyTerm_zero_ball ((Z1_7_0Half_sound 1) ((2,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z1_7_0Half_sound 1) ((3,0) : PairSlot))) (entropyTerm_zero_ball ((Z1_7_0Half_sound 1) ((3,1) : PairSlot))) (entropyTerm_zero_ball ((Z1_7_0Half_sound 1) ((3,2) : PairSlot))) (entropyTerm_zero_ball ((Z1_7_0Half_sound 1) ((3,3) : PairSlot))) (entropyTerm_zero_ball ((Z1_7_0Half_sound 1) ((3,4) : PairSlot))) (entropyTerm_zero_ball ((Z1_7_0Half_sound 1) ((3,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z1_7_0Half_sound 1) ((4,0) : PairSlot))) (entropyTerm_zero_ball ((Z1_7_0Half_sound 1) ((4,1) : PairSlot))) (entropyTerm_zero_ball ((Z1_7_0Half_sound 1) ((4,2) : PairSlot))) (entropyTerm_zero_ball ((Z1_7_0Half_sound 1) ((4,3) : PairSlot))) (entropyTerm_zero_ball ((Z1_7_0Half_sound 1) ((4,4) : PairSlot))) Z1_7_0H1E_4_5_sound
  · exact forall_fin6 (entropyTerm_zero_ball ((Z1_7_0Half_sound 1) ((5,0) : PairSlot))) (entropyTerm_zero_ball ((Z1_7_0Half_sound 1) ((5,1) : PairSlot))) (entropyTerm_zero_ball ((Z1_7_0Half_sound 1) ((5,2) : PairSlot))) (entropyTerm_zero_ball ((Z1_7_0Half_sound 1) ((5,3) : PairSlot))) Z1_7_0H1E_5_4_sound (entropyTerm_zero_ball ((Z1_7_0Half_sound 1) ((5,5) : PairSlot)))
lemma Z1_7_0H1Entropy_sound : Z1_7_0H1Entropy.Encloses (Foundation.finiteEntropy Z1_7_0H1Value) := by
  exact contains_sound (entropyPair_enclosed Z1_7_0H1Value Z1_7_0H1Terms Z1_7_0H1Terms_sound) (by decide +kernel)
lemma Z1_7_0H1Mass_sound : Z1_7_0H1Mass.Encloses (∑ a, Z1_7_0H1Value a) := by
  exact contains_sound (pairSumBall_sound (Z1_7_0Half 1) Z1_7_0H1Value (Z1_7_0Half_sound 1)) (by decide +kernel)
lemma Z1_7_0H1MassTermLog_sound : Z1_7_0H1MassTermLog.Encloses (Real.log ((∑ a, Z1_7_0H1Value a))) := by
  exact log_exact_one_ball (Z1_7_0H1Mass_sound)
lemma Z1_7_0H1MassTerm_sound : Z1_7_0H1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, Z1_7_0H1Value a))) := by
  exact contains_sound (entropyTerm_ball (Z1_7_0H1Mass_sound) Z1_7_0H1MassTermLog_sound) (by decide +kernel)
lemma Z1_7_0H1H_sound : Z1_7_0H1H.Encloses (homogeneousEntropy Z1_7_0H1Value) := by
  exact contains_sound (homogeneous_enclosed Z1_7_0H1Value Z1_7_0H1MassTerm_sound Z1_7_0H1Entropy_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Four2_6_0
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
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
lemma Z2_6_0Raw_sound_0 (j : Fin 6) :
    (Z2_6_0Raw (0,j)).Encloses (weight (orderedPairInteger (shape 2 6 0) 0 j) : ℝ) := by
  fin_cases j
  · change (Z2_6_0Raw (0,0)).Encloses (weight (orderedPairInteger (shape 2 6 0) 0 0) : ℝ)
    have he : orderedPairInteger (shape 2 6 0) 0 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_6_0Raw (0,1)).Encloses (weight (orderedPairInteger (shape 2 6 0) 0 1) : ℝ)
    have he : orderedPairInteger (shape 2 6 0) 0 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_6_0Raw (0,2)).Encloses (weight (orderedPairInteger (shape 2 6 0) 0 2) : ℝ)
    have he : orderedPairInteger (shape 2 6 0) 0 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_6_0Raw (0,3)).Encloses (weight (orderedPairInteger (shape 2 6 0) 0 3) : ℝ)
    have he : orderedPairInteger (shape 2 6 0) 0 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_6_0Raw (0,4)).Encloses (weight (orderedPairInteger (shape 2 6 0) 0 4) : ℝ)
    have he : orderedPairInteger (shape 2 6 0) 0 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_6_0Raw (0,5)).Encloses (weight (orderedPairInteger (shape 2 6 0) 0 5) : ℝ)
    have he : orderedPairInteger (shape 2 6 0) 0 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z2_6_0Raw_sound_1 (j : Fin 6) :
    (Z2_6_0Raw (1,j)).Encloses (weight (orderedPairInteger (shape 2 6 0) 1 j) : ℝ) := by
  fin_cases j
  · change (Z2_6_0Raw (1,0)).Encloses (weight (orderedPairInteger (shape 2 6 0) 1 0) : ℝ)
    have he : orderedPairInteger (shape 2 6 0) 1 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_6_0Raw (1,1)).Encloses (weight (orderedPairInteger (shape 2 6 0) 1 1) : ℝ)
    have he : orderedPairInteger (shape 2 6 0) 1 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_6_0Raw (1,2)).Encloses (weight (orderedPairInteger (shape 2 6 0) 1 2) : ℝ)
    have he : orderedPairInteger (shape 2 6 0) 1 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_6_0Raw (1,3)).Encloses (weight (orderedPairInteger (shape 2 6 0) 1 3) : ℝ)
    have he : orderedPairInteger (shape 2 6 0) 1 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_6_0Raw (1,4)).Encloses (weight (orderedPairInteger (shape 2 6 0) 1 4) : ℝ)
    have he : orderedPairInteger (shape 2 6 0) 1 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_6_0Raw (1,5)).Encloses (weight (orderedPairInteger (shape 2 6 0) 1 5) : ℝ)
    have he : orderedPairInteger (shape 2 6 0) 1 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z2_6_0Raw_sound_2 (j : Fin 6) :
    (Z2_6_0Raw (2,j)).Encloses (weight (orderedPairInteger (shape 2 6 0) 2 j) : ℝ) := by
  fin_cases j
  · change (Z2_6_0Raw (2,0)).Encloses (weight (orderedPairInteger (shape 2 6 0) 2 0) : ℝ)
    have he : orderedPairInteger (shape 2 6 0) 2 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_6_0Raw (2,1)).Encloses (weight (orderedPairInteger (shape 2 6 0) 2 1) : ℝ)
    have he : orderedPairInteger (shape 2 6 0) 2 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_6_0Raw (2,2)).Encloses (weight (orderedPairInteger (shape 2 6 0) 2 2) : ℝ)
    have he : orderedPairInteger (shape 2 6 0) 2 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_6_0Raw (2,3)).Encloses (weight (orderedPairInteger (shape 2 6 0) 2 3) : ℝ)
    have he : orderedPairInteger (shape 2 6 0) 2 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_6_0Raw (2,4)).Encloses (weight (orderedPairInteger (shape 2 6 0) 2 4) : ℝ)
    have he : orderedPairInteger (shape 2 6 0) 2 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_6_0Raw (2,5)).Encloses (weight (orderedPairInteger (shape 2 6 0) 2 5) : ℝ)
    have he : orderedPairInteger (shape 2 6 0) 2 5 = (-12708) := by decide +kernel
    rw [he]
    exact w122_sound
lemma Z2_6_0Raw_sound_3 (j : Fin 6) :
    (Z2_6_0Raw (3,j)).Encloses (weight (orderedPairInteger (shape 2 6 0) 3 j) : ℝ) := by
  fin_cases j
  · change (Z2_6_0Raw (3,0)).Encloses (weight (orderedPairInteger (shape 2 6 0) 3 0) : ℝ)
    have he : orderedPairInteger (shape 2 6 0) 3 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_6_0Raw (3,1)).Encloses (weight (orderedPairInteger (shape 2 6 0) 3 1) : ℝ)
    have he : orderedPairInteger (shape 2 6 0) 3 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_6_0Raw (3,2)).Encloses (weight (orderedPairInteger (shape 2 6 0) 3 2) : ℝ)
    have he : orderedPairInteger (shape 2 6 0) 3 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_6_0Raw (3,3)).Encloses (weight (orderedPairInteger (shape 2 6 0) 3 3) : ℝ)
    have he : orderedPairInteger (shape 2 6 0) 3 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_6_0Raw (3,4)).Encloses (weight (orderedPairInteger (shape 2 6 0) 3 4) : ℝ)
    have he : orderedPairInteger (shape 2 6 0) 3 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_6_0Raw (3,5)).Encloses (weight (orderedPairInteger (shape 2 6 0) 3 5) : ℝ)
    have he : orderedPairInteger (shape 2 6 0) 3 5 = (-36610) := by decide +kernel
    rw [he]
    exact w49_sound
lemma Z2_6_0Raw_sound_4 (j : Fin 6) :
    (Z2_6_0Raw (4,j)).Encloses (weight (orderedPairInteger (shape 2 6 0) 4 j) : ℝ) := by
  fin_cases j
  · change (Z2_6_0Raw (4,0)).Encloses (weight (orderedPairInteger (shape 2 6 0) 4 0) : ℝ)
    have he : orderedPairInteger (shape 2 6 0) 4 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_6_0Raw (4,1)).Encloses (weight (orderedPairInteger (shape 2 6 0) 4 1) : ℝ)
    have he : orderedPairInteger (shape 2 6 0) 4 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_6_0Raw (4,2)).Encloses (weight (orderedPairInteger (shape 2 6 0) 4 2) : ℝ)
    have he : orderedPairInteger (shape 2 6 0) 4 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_6_0Raw (4,3)).Encloses (weight (orderedPairInteger (shape 2 6 0) 4 3) : ℝ)
    have he : orderedPairInteger (shape 2 6 0) 4 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_6_0Raw (4,4)).Encloses (weight (orderedPairInteger (shape 2 6 0) 4 4) : ℝ)
    have he : orderedPairInteger (shape 2 6 0) 4 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_6_0Raw (4,5)).Encloses (weight (orderedPairInteger (shape 2 6 0) 4 5) : ℝ)
    have he : orderedPairInteger (shape 2 6 0) 4 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z2_6_0Raw_sound_5 (j : Fin 6) :
    (Z2_6_0Raw (5,j)).Encloses (weight (orderedPairInteger (shape 2 6 0) 5 j) : ℝ) := by
  fin_cases j
  · change (Z2_6_0Raw (5,0)).Encloses (weight (orderedPairInteger (shape 2 6 0) 5 0) : ℝ)
    have he : orderedPairInteger (shape 2 6 0) 5 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_6_0Raw (5,1)).Encloses (weight (orderedPairInteger (shape 2 6 0) 5 1) : ℝ)
    have he : orderedPairInteger (shape 2 6 0) 5 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_6_0Raw (5,2)).Encloses (weight (orderedPairInteger (shape 2 6 0) 5 2) : ℝ)
    have he : orderedPairInteger (shape 2 6 0) 5 2 = (-12708) := by decide +kernel
    rw [he]
    exact w122_sound
  · change (Z2_6_0Raw (5,3)).Encloses (weight (orderedPairInteger (shape 2 6 0) 5 3) : ℝ)
    have he : orderedPairInteger (shape 2 6 0) 5 3 = (-36610) := by decide +kernel
    rw [he]
    exact w49_sound
  · change (Z2_6_0Raw (5,4)).Encloses (weight (orderedPairInteger (shape 2 6 0) 5 4) : ℝ)
    have he : orderedPairInteger (shape 2 6 0) 5 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_6_0Raw (5,5)).Encloses (weight (orderedPairInteger (shape 2 6 0) 5 5) : ℝ)
    have he : orderedPairInteger (shape 2 6 0) 5 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z2_6_0Raw_sound (ij : PairSlot) :
    (Z2_6_0Raw ij).Encloses (weight (orderedPairInteger (shape 2 6 0) ij.1 ij.2) : ℝ) := by
  rcases ij with ⟨i,j⟩
  revert i
  exact forall_fin6 (Z2_6_0Raw_sound_0 j) (Z2_6_0Raw_sound_1 j) (Z2_6_0Raw_sound_2 j) (Z2_6_0Raw_sound_3 j) (Z2_6_0Raw_sound_4 j) (Z2_6_0Raw_sound_5 j)
lemma Z2_6_0Den_sound : Z2_6_0Den.Encloses
    (((orderedPairs (shape 2 6 0)).map (fun ij => weight (orderedPairInteger (shape 2 6 0) ij.1 ij.2))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (orderedPairs (shape 2 6 0)) Z2_6_0Raw
    (fun ij => weight (orderedPairInteger (shape 2 6 0) ij.1 ij.2))
    (fun ij _ => Z2_6_0Raw_sound ij)) (by decide +kernel)
lemma Z2_6_0Den_pos : 0 < Z2_6_0Den.lower := by decide +kernel
lemma Z2_6_0Contains : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j = shapeMax (shape 2 6 0) →
    contains (.mul (Z2_6_0Raw (i,j)) (.inv Z2_6_0Den)) (Z2_6_0Probs (i,j)) = true := by
  decide +kernel
lemma Z2_6_0Zero : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j ≠ shapeMax (shape 2 6 0) → Z2_6_0Probs (i,j) = .exact 0 := by
  decide +kernel
lemma Z2_6_0Probs_sound (ij : PairSlot) :
    (Z2_6_0Probs ij).Encloses (zeroPairLaw (shape 2 6 0) ij.1 ij.2 : ℝ) := by
  by_cases h : statisticWeight ij.1 + statisticWeight ij.2 = shapeMax (shape 2 6 0)
  · have hb := contains_sound (Ball.mul_sound (Z2_6_0Raw_sound ij)
      (Ball.inv_sound Z2_6_0Den_sound Z2_6_0Den_pos)) (Z2_6_0Contains ij.1 ij.2 h)
    simpa only [zeroPairLaw, h, ite_true, if_true, Rat.cast_div, Rat.cast_mul,
      Rat.cast_inv, div_eq_mul_inv] using hb
  · rw [Z2_6_0Zero ij.1 ij.2 h]
    simpa only [zeroPairLaw, h, ite_false, if_false] using Ball.exact_sound 0

lemma Z2_6_0Half_sound (w : Fin 3) (ij : PairSlot) :
    (Z2_6_0Half w ij).Encloses (halfLaw (shape 2 6 0) w ij : ℝ) := by
  have hp : positive (shape 2 6 0) = false := by decide +kernel
  simp only [Z2_6_0Half, halfLaw, hp, Bool.false_eq_true, ite_false, if_false]
  split_ifs
  · exact Ball.exact_sound 1
  · exact Ball.exact_sound 0
  · exact Z2_6_0Probs_sound _
  · exact Z2_6_0Probs_sound _

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
lemma Z2_6_0H1E_2_5Log_sound : Z2_6_0H1E_2_5Log.Encloses (Real.log (Z2_6_0H1Value ((2,5) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z2_6_0Half_sound 1) ((2,5) : PairSlot)) (w := Z2_6_0H1E_2_5LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z2_6_0H1E_2_5_sound : Z2_6_0H1E_2_5.Encloses (Foundation.entropyTerm (Z2_6_0H1Value ((2,5) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z2_6_0Half_sound 1) ((2,5) : PairSlot)) Z2_6_0H1E_2_5Log_sound) (by decide +kernel)
lemma Z2_6_0H1E_3_5Log_sound : Z2_6_0H1E_3_5Log.Encloses (Real.log (Z2_6_0H1Value ((3,5) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z2_6_0Half_sound 1) ((3,5) : PairSlot)) (w := Z2_6_0H1E_3_5LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z2_6_0H1E_3_5_sound : Z2_6_0H1E_3_5.Encloses (Foundation.entropyTerm (Z2_6_0H1Value ((3,5) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z2_6_0Half_sound 1) ((3,5) : PairSlot)) Z2_6_0H1E_3_5Log_sound) (by decide +kernel)
lemma Z2_6_0H1E_4_4Log_sound : Z2_6_0H1E_4_4Log.Encloses (Real.log (Z2_6_0H1Value ((4,4) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z2_6_0Half_sound 1) ((4,4) : PairSlot)) (w := Z2_6_0H1E_4_4LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z2_6_0H1E_4_4_sound : Z2_6_0H1E_4_4.Encloses (Foundation.entropyTerm (Z2_6_0H1Value ((4,4) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z2_6_0Half_sound 1) ((4,4) : PairSlot)) Z2_6_0H1E_4_4Log_sound) (by decide +kernel)
lemma Z2_6_0H1E_5_2Log_sound : Z2_6_0H1E_5_2Log.Encloses (Real.log (Z2_6_0H1Value ((5,2) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z2_6_0Half_sound 1) ((5,2) : PairSlot)) (w := Z2_6_0H1E_5_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z2_6_0H1E_5_2_sound : Z2_6_0H1E_5_2.Encloses (Foundation.entropyTerm (Z2_6_0H1Value ((5,2) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z2_6_0Half_sound 1) ((5,2) : PairSlot)) Z2_6_0H1E_5_2Log_sound) (by decide +kernel)
lemma Z2_6_0H1E_5_3Log_sound : Z2_6_0H1E_5_3Log.Encloses (Real.log (Z2_6_0H1Value ((5,3) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z2_6_0Half_sound 1) ((5,3) : PairSlot)) (w := Z2_6_0H1E_5_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z2_6_0H1E_5_3_sound : Z2_6_0H1E_5_3.Encloses (Foundation.entropyTerm (Z2_6_0H1Value ((5,3) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z2_6_0Half_sound 1) ((5,3) : PairSlot)) Z2_6_0H1E_5_3Log_sound) (by decide +kernel)
lemma Z2_6_0H1Terms_sound (a : PairSlot) :
    (Z2_6_0H1Terms a).Encloses (Foundation.entropyTerm (Z2_6_0H1Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (entropyTerm_zero_ball ((Z2_6_0Half_sound 1) ((0,0) : PairSlot))) (entropyTerm_zero_ball ((Z2_6_0Half_sound 1) ((0,1) : PairSlot))) (entropyTerm_zero_ball ((Z2_6_0Half_sound 1) ((0,2) : PairSlot))) (entropyTerm_zero_ball ((Z2_6_0Half_sound 1) ((0,3) : PairSlot))) (entropyTerm_zero_ball ((Z2_6_0Half_sound 1) ((0,4) : PairSlot))) (entropyTerm_zero_ball ((Z2_6_0Half_sound 1) ((0,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z2_6_0Half_sound 1) ((1,0) : PairSlot))) (entropyTerm_zero_ball ((Z2_6_0Half_sound 1) ((1,1) : PairSlot))) (entropyTerm_zero_ball ((Z2_6_0Half_sound 1) ((1,2) : PairSlot))) (entropyTerm_zero_ball ((Z2_6_0Half_sound 1) ((1,3) : PairSlot))) (entropyTerm_zero_ball ((Z2_6_0Half_sound 1) ((1,4) : PairSlot))) (entropyTerm_zero_ball ((Z2_6_0Half_sound 1) ((1,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z2_6_0Half_sound 1) ((2,0) : PairSlot))) (entropyTerm_zero_ball ((Z2_6_0Half_sound 1) ((2,1) : PairSlot))) (entropyTerm_zero_ball ((Z2_6_0Half_sound 1) ((2,2) : PairSlot))) (entropyTerm_zero_ball ((Z2_6_0Half_sound 1) ((2,3) : PairSlot))) (entropyTerm_zero_ball ((Z2_6_0Half_sound 1) ((2,4) : PairSlot))) Z2_6_0H1E_2_5_sound
  · exact forall_fin6 (entropyTerm_zero_ball ((Z2_6_0Half_sound 1) ((3,0) : PairSlot))) (entropyTerm_zero_ball ((Z2_6_0Half_sound 1) ((3,1) : PairSlot))) (entropyTerm_zero_ball ((Z2_6_0Half_sound 1) ((3,2) : PairSlot))) (entropyTerm_zero_ball ((Z2_6_0Half_sound 1) ((3,3) : PairSlot))) (entropyTerm_zero_ball ((Z2_6_0Half_sound 1) ((3,4) : PairSlot))) Z2_6_0H1E_3_5_sound
  · exact forall_fin6 (entropyTerm_zero_ball ((Z2_6_0Half_sound 1) ((4,0) : PairSlot))) (entropyTerm_zero_ball ((Z2_6_0Half_sound 1) ((4,1) : PairSlot))) (entropyTerm_zero_ball ((Z2_6_0Half_sound 1) ((4,2) : PairSlot))) (entropyTerm_zero_ball ((Z2_6_0Half_sound 1) ((4,3) : PairSlot))) Z2_6_0H1E_4_4_sound (entropyTerm_zero_ball ((Z2_6_0Half_sound 1) ((4,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z2_6_0Half_sound 1) ((5,0) : PairSlot))) (entropyTerm_zero_ball ((Z2_6_0Half_sound 1) ((5,1) : PairSlot))) Z2_6_0H1E_5_2_sound Z2_6_0H1E_5_3_sound (entropyTerm_zero_ball ((Z2_6_0Half_sound 1) ((5,4) : PairSlot))) (entropyTerm_zero_ball ((Z2_6_0Half_sound 1) ((5,5) : PairSlot)))
lemma Z2_6_0H1Entropy_sound : Z2_6_0H1Entropy.Encloses (Foundation.finiteEntropy Z2_6_0H1Value) := by
  exact contains_sound (entropyPair_enclosed Z2_6_0H1Value Z2_6_0H1Terms Z2_6_0H1Terms_sound) (by decide +kernel)
lemma Z2_6_0H1Mass_sound : Z2_6_0H1Mass.Encloses (∑ a, Z2_6_0H1Value a) := by
  exact contains_sound (pairSumBall_sound (Z2_6_0Half 1) Z2_6_0H1Value (Z2_6_0Half_sound 1)) (by decide +kernel)
lemma Z2_6_0H1MassTermLog_sound : Z2_6_0H1MassTermLog.Encloses (Real.log ((∑ a, Z2_6_0H1Value a))) := by
  exact checkLog_sound logTwoBall_sound (Z2_6_0H1Mass_sound) (w := Z2_6_0H1MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z2_6_0H1MassTerm_sound : Z2_6_0H1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, Z2_6_0H1Value a))) := by
  exact contains_sound (entropyTerm_ball (Z2_6_0H1Mass_sound) Z2_6_0H1MassTermLog_sound) (by decide +kernel)
lemma Z2_6_0H1H_sound : Z2_6_0H1H.Encloses (homogeneousEntropy Z2_6_0H1Value) := by
  exact contains_sound (homogeneous_enclosed Z2_6_0H1Value Z2_6_0H1MassTerm_sound Z2_6_0H1Entropy_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitA2_7_7
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
lemma A2_7_7_below : below (shape 2 7 7) = [
  (shape 0 1 7),
  (shape 0 2 6),
  (shape 0 3 5),
  (shape 0 4 4),
  (shape 0 5 3),
  (shape 0 6 2),
  (shape 0 7 1),
  (shape 1 0 7),
  (shape 1 1 6),
  (shape 1 2 5),
  (shape 1 3 4),
  (shape 1 4 3),
  (shape 1 5 2),
  (shape 1 6 1),
  (shape 1 7 0),
  (shape 2 0 6),
  (shape 2 1 5),
  (shape 2 2 4),
  (shape 2 3 3),
  (shape 2 4 2),
  (shape 2 5 1),
  (shape 2 6 0)] := by decide +kernel

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA2_7_7I1
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
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
lemma CA2_7_7I1Singles_sound (u : Shape) (hu : u ∈ below (shape 2 7 7))
    (hd : designated (Equiv.refl (Fin 3)) 1 u) :
    (CA2_7_7I1Singles u).Encloses (homogeneousEntropy ((fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) u)) := by
  rw [A2_7_7_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 1 7) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 2 6) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 3 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 4 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 5 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 6 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 7 1) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 0 7) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 1 6) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 2 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 3 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 4 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 5 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 6 1) by decide +kernel) hd |>.elim
  · exact Z1_7_0H1H_sound
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 2 0 6) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 2 1 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 2 2 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 2 3 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 2 4 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 2 5 1) by decide +kernel) hd |>.elim
  · exact Z2_6_0H1H_sound
lemma CA2_7_7I1Singleton_sound_oai : CA2_7_7I1Singleton.Encloses
    (singletonEntropy (below (shape 2 7 7)) (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 2 7 7)) A2_7_7Law (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1
    CA2_7_7I1Singles (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_7_7Law_sound u) CA2_7_7I1Singles_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_7_7I1Singleton_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_7_7I1Singleton_sound_oai
