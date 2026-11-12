-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z4_4_0Four_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:22:46.578721+00:00
-- url     : https://prove2.me/submissions/8dc43676-08b6-44de-b1d3-a5c99a23dcf0

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
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Four0_3_5
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
lemma w204_sound : w204.Encloses (weight (22176) : ℝ) := by
  exact weight_enclosed_of_trace (22176) w204Trace w204S0 w204S1 w204S2 w204S3 w204S4 w204S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w212_sound : w212.Encloses (weight (28778) : ℝ) := by
  exact weight_enclosed_of_trace (28778) w212Trace w212S0 w212S1 w212S2 w212S3 w212S4 w212S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w221_sound : w221.Encloses (weight (44147) : ℝ) := by
  exact weight_enclosed_of_trace (44147) w221Trace w221S0 w221S1 w221S2 w221S3 w221S4 w221S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

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
lemma w123_sound : w123.Encloses (weight (-12216) : ℝ) := by
  exact weight_enclosed_of_trace (-12216) w123Trace w123S0 w123S1 w123S2 w123S3 w123S4 w123S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Four4_4_0
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
lemma Z4_4_0Raw_sound_0 (j : Fin 6) :
    (Z4_4_0Raw (0,j)).Encloses (weight (orderedPairInteger (shape 4 4 0) 0 j) : ℝ) := by
  fin_cases j
  · change (Z4_4_0Raw (0,0)).Encloses (weight (orderedPairInteger (shape 4 4 0) 0 0) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 0 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_4_0Raw (0,1)).Encloses (weight (orderedPairInteger (shape 4 4 0) 0 1) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 0 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_4_0Raw (0,2)).Encloses (weight (orderedPairInteger (shape 4 4 0) 0 2) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 0 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_4_0Raw (0,3)).Encloses (weight (orderedPairInteger (shape 4 4 0) 0 3) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 0 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_4_0Raw (0,4)).Encloses (weight (orderedPairInteger (shape 4 4 0) 0 4) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 0 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_4_0Raw (0,5)).Encloses (weight (orderedPairInteger (shape 4 4 0) 0 5) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 0 5 = (-12216) := by decide +kernel
    rw [he]
    exact w123_sound
lemma Z4_4_0Raw_sound_1 (j : Fin 6) :
    (Z4_4_0Raw (1,j)).Encloses (weight (orderedPairInteger (shape 4 4 0) 1 j) : ℝ) := by
  fin_cases j
  · change (Z4_4_0Raw (1,0)).Encloses (weight (orderedPairInteger (shape 4 4 0) 1 0) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 1 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_4_0Raw (1,1)).Encloses (weight (orderedPairInteger (shape 4 4 0) 1 1) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 1 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_4_0Raw (1,2)).Encloses (weight (orderedPairInteger (shape 4 4 0) 1 2) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 1 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_4_0Raw (1,3)).Encloses (weight (orderedPairInteger (shape 4 4 0) 1 3) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 1 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_4_0Raw (1,4)).Encloses (weight (orderedPairInteger (shape 4 4 0) 1 4) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 1 4 = (28778) := by decide +kernel
    rw [he]
    exact w212_sound
  · change (Z4_4_0Raw (1,5)).Encloses (weight (orderedPairInteger (shape 4 4 0) 1 5) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 1 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z4_4_0Raw_sound_2 (j : Fin 6) :
    (Z4_4_0Raw (2,j)).Encloses (weight (orderedPairInteger (shape 4 4 0) 2 j) : ℝ) := by
  fin_cases j
  · change (Z4_4_0Raw (2,0)).Encloses (weight (orderedPairInteger (shape 4 4 0) 2 0) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 2 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_4_0Raw (2,1)).Encloses (weight (orderedPairInteger (shape 4 4 0) 2 1) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 2 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_4_0Raw (2,2)).Encloses (weight (orderedPairInteger (shape 4 4 0) 2 2) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 2 2 = (44147) := by decide +kernel
    rw [he]
    exact w221_sound
  · change (Z4_4_0Raw (2,3)).Encloses (weight (orderedPairInteger (shape 4 4 0) 2 3) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 2 3 = (22176) := by decide +kernel
    rw [he]
    exact w204_sound
  · change (Z4_4_0Raw (2,4)).Encloses (weight (orderedPairInteger (shape 4 4 0) 2 4) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 2 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_4_0Raw (2,5)).Encloses (weight (orderedPairInteger (shape 4 4 0) 2 5) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 2 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z4_4_0Raw_sound_3 (j : Fin 6) :
    (Z4_4_0Raw (3,j)).Encloses (weight (orderedPairInteger (shape 4 4 0) 3 j) : ℝ) := by
  fin_cases j
  · change (Z4_4_0Raw (3,0)).Encloses (weight (orderedPairInteger (shape 4 4 0) 3 0) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 3 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_4_0Raw (3,1)).Encloses (weight (orderedPairInteger (shape 4 4 0) 3 1) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 3 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_4_0Raw (3,2)).Encloses (weight (orderedPairInteger (shape 4 4 0) 3 2) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 3 2 = (22176) := by decide +kernel
    rw [he]
    exact w204_sound
  · change (Z4_4_0Raw (3,3)).Encloses (weight (orderedPairInteger (shape 4 4 0) 3 3) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 3 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_4_0Raw (3,4)).Encloses (weight (orderedPairInteger (shape 4 4 0) 3 4) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 3 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_4_0Raw (3,5)).Encloses (weight (orderedPairInteger (shape 4 4 0) 3 5) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 3 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z4_4_0Raw_sound_4 (j : Fin 6) :
    (Z4_4_0Raw (4,j)).Encloses (weight (orderedPairInteger (shape 4 4 0) 4 j) : ℝ) := by
  fin_cases j
  · change (Z4_4_0Raw (4,0)).Encloses (weight (orderedPairInteger (shape 4 4 0) 4 0) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 4 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_4_0Raw (4,1)).Encloses (weight (orderedPairInteger (shape 4 4 0) 4 1) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 4 1 = (28778) := by decide +kernel
    rw [he]
    exact w212_sound
  · change (Z4_4_0Raw (4,2)).Encloses (weight (orderedPairInteger (shape 4 4 0) 4 2) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 4 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_4_0Raw (4,3)).Encloses (weight (orderedPairInteger (shape 4 4 0) 4 3) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 4 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_4_0Raw (4,4)).Encloses (weight (orderedPairInteger (shape 4 4 0) 4 4) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 4 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_4_0Raw (4,5)).Encloses (weight (orderedPairInteger (shape 4 4 0) 4 5) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 4 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z4_4_0Raw_sound_5 (j : Fin 6) :
    (Z4_4_0Raw (5,j)).Encloses (weight (orderedPairInteger (shape 4 4 0) 5 j) : ℝ) := by
  fin_cases j
  · change (Z4_4_0Raw (5,0)).Encloses (weight (orderedPairInteger (shape 4 4 0) 5 0) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 5 0 = (-12216) := by decide +kernel
    rw [he]
    exact w123_sound
  · change (Z4_4_0Raw (5,1)).Encloses (weight (orderedPairInteger (shape 4 4 0) 5 1) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 5 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_4_0Raw (5,2)).Encloses (weight (orderedPairInteger (shape 4 4 0) 5 2) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 5 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_4_0Raw (5,3)).Encloses (weight (orderedPairInteger (shape 4 4 0) 5 3) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 5 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_4_0Raw (5,4)).Encloses (weight (orderedPairInteger (shape 4 4 0) 5 4) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 5 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_4_0Raw (5,5)).Encloses (weight (orderedPairInteger (shape 4 4 0) 5 5) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 5 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z4_4_0Raw_sound (ij : PairSlot) :
    (Z4_4_0Raw ij).Encloses (weight (orderedPairInteger (shape 4 4 0) ij.1 ij.2) : ℝ) := by
  rcases ij with ⟨i,j⟩
  revert i
  exact forall_fin6 (Z4_4_0Raw_sound_0 j) (Z4_4_0Raw_sound_1 j) (Z4_4_0Raw_sound_2 j) (Z4_4_0Raw_sound_3 j) (Z4_4_0Raw_sound_4 j) (Z4_4_0Raw_sound_5 j)
lemma Z4_4_0Den_sound : Z4_4_0Den.Encloses
    (((orderedPairs (shape 4 4 0)).map (fun ij => weight (orderedPairInteger (shape 4 4 0) ij.1 ij.2))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (orderedPairs (shape 4 4 0)) Z4_4_0Raw
    (fun ij => weight (orderedPairInteger (shape 4 4 0) ij.1 ij.2))
    (fun ij _ => Z4_4_0Raw_sound ij)) (by decide +kernel)
lemma Z4_4_0Den_pos : 0 < Z4_4_0Den.lower := by decide +kernel
lemma Z4_4_0Contains : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j = shapeMax (shape 4 4 0) →
    contains (.mul (Z4_4_0Raw (i,j)) (.inv Z4_4_0Den)) (Z4_4_0Probs (i,j)) = true := by
  decide +kernel
lemma Z4_4_0Zero : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j ≠ shapeMax (shape 4 4 0) → Z4_4_0Probs (i,j) = .exact 0 := by
  decide +kernel
lemma Z4_4_0Probs_sound (ij : PairSlot) :
    (Z4_4_0Probs ij).Encloses (zeroPairLaw (shape 4 4 0) ij.1 ij.2 : ℝ) := by
  by_cases h : statisticWeight ij.1 + statisticWeight ij.2 = shapeMax (shape 4 4 0)
  · have hb := contains_sound (Ball.mul_sound (Z4_4_0Raw_sound ij)
      (Ball.inv_sound Z4_4_0Den_sound Z4_4_0Den_pos)) (Z4_4_0Contains ij.1 ij.2 h)
    simpa only [zeroPairLaw, h, ite_true, if_true, Rat.cast_div, Rat.cast_mul,
      Rat.cast_inv, div_eq_mul_inv] using hb
  · rw [Z4_4_0Zero ij.1 ij.2 h]
    simpa only [zeroPairLaw, h, ite_false, if_false] using Ball.exact_sound 0

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
lemma Z4_4_0E_0_5Log_sound : Z4_4_0E_0_5Log.Encloses (Real.log (Z4_4_0Value ((0,5) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z4_4_0Probs_sound ((0,5) : PairSlot)) (w := Z4_4_0E_0_5LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z4_4_0E_0_5_sound : Z4_4_0E_0_5.Encloses (Foundation.entropyTerm (Z4_4_0Value ((0,5) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z4_4_0Probs_sound ((0,5) : PairSlot)) Z4_4_0E_0_5Log_sound) (by decide +kernel)
lemma Z4_4_0E_1_4Log_sound : Z4_4_0E_1_4Log.Encloses (Real.log (Z4_4_0Value ((1,4) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z4_4_0Probs_sound ((1,4) : PairSlot)) (w := Z4_4_0E_1_4LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z4_4_0E_1_4_sound : Z4_4_0E_1_4.Encloses (Foundation.entropyTerm (Z4_4_0Value ((1,4) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z4_4_0Probs_sound ((1,4) : PairSlot)) Z4_4_0E_1_4Log_sound) (by decide +kernel)
lemma Z4_4_0E_2_2Log_sound : Z4_4_0E_2_2Log.Encloses (Real.log (Z4_4_0Value ((2,2) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z4_4_0Probs_sound ((2,2) : PairSlot)) (w := Z4_4_0E_2_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z4_4_0E_2_2_sound : Z4_4_0E_2_2.Encloses (Foundation.entropyTerm (Z4_4_0Value ((2,2) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z4_4_0Probs_sound ((2,2) : PairSlot)) Z4_4_0E_2_2Log_sound) (by decide +kernel)
lemma Z4_4_0E_2_3Log_sound : Z4_4_0E_2_3Log.Encloses (Real.log (Z4_4_0Value ((2,3) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z4_4_0Probs_sound ((2,3) : PairSlot)) (w := Z4_4_0E_2_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z4_4_0E_2_3_sound : Z4_4_0E_2_3.Encloses (Foundation.entropyTerm (Z4_4_0Value ((2,3) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z4_4_0Probs_sound ((2,3) : PairSlot)) Z4_4_0E_2_3Log_sound) (by decide +kernel)
lemma Z4_4_0E_3_2Log_sound : Z4_4_0E_3_2Log.Encloses (Real.log (Z4_4_0Value ((3,2) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z4_4_0Probs_sound ((3,2) : PairSlot)) (w := Z4_4_0E_3_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z4_4_0E_3_2_sound : Z4_4_0E_3_2.Encloses (Foundation.entropyTerm (Z4_4_0Value ((3,2) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z4_4_0Probs_sound ((3,2) : PairSlot)) Z4_4_0E_3_2Log_sound) (by decide +kernel)
lemma Z4_4_0E_3_3Log_sound : Z4_4_0E_3_3Log.Encloses (Real.log (Z4_4_0Value ((3,3) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z4_4_0Probs_sound ((3,3) : PairSlot)) (w := Z4_4_0E_3_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z4_4_0E_3_3_sound : Z4_4_0E_3_3.Encloses (Foundation.entropyTerm (Z4_4_0Value ((3,3) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z4_4_0Probs_sound ((3,3) : PairSlot)) Z4_4_0E_3_3Log_sound) (by decide +kernel)
lemma Z4_4_0E_4_1Log_sound : Z4_4_0E_4_1Log.Encloses (Real.log (Z4_4_0Value ((4,1) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z4_4_0Probs_sound ((4,1) : PairSlot)) (w := Z4_4_0E_4_1LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z4_4_0E_4_1_sound : Z4_4_0E_4_1.Encloses (Foundation.entropyTerm (Z4_4_0Value ((4,1) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z4_4_0Probs_sound ((4,1) : PairSlot)) Z4_4_0E_4_1Log_sound) (by decide +kernel)
lemma Z4_4_0E_5_0Log_sound : Z4_4_0E_5_0Log.Encloses (Real.log (Z4_4_0Value ((5,0) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z4_4_0Probs_sound ((5,0) : PairSlot)) (w := Z4_4_0E_5_0LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z4_4_0E_5_0_sound : Z4_4_0E_5_0.Encloses (Foundation.entropyTerm (Z4_4_0Value ((5,0) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z4_4_0Probs_sound ((5,0) : PairSlot)) Z4_4_0E_5_0Log_sound) (by decide +kernel)
lemma Z4_4_0Terms_sound (a : PairSlot) :
    (Z4_4_0Terms a).Encloses (Foundation.entropyTerm (Z4_4_0Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (entropyTerm_zero_ball (Z4_4_0Probs_sound ((0,0) : PairSlot))) (entropyTerm_zero_ball (Z4_4_0Probs_sound ((0,1) : PairSlot))) (entropyTerm_zero_ball (Z4_4_0Probs_sound ((0,2) : PairSlot))) (entropyTerm_zero_ball (Z4_4_0Probs_sound ((0,3) : PairSlot))) (entropyTerm_zero_ball (Z4_4_0Probs_sound ((0,4) : PairSlot))) Z4_4_0E_0_5_sound
  · exact forall_fin6 (entropyTerm_zero_ball (Z4_4_0Probs_sound ((1,0) : PairSlot))) (entropyTerm_zero_ball (Z4_4_0Probs_sound ((1,1) : PairSlot))) (entropyTerm_zero_ball (Z4_4_0Probs_sound ((1,2) : PairSlot))) (entropyTerm_zero_ball (Z4_4_0Probs_sound ((1,3) : PairSlot))) Z4_4_0E_1_4_sound (entropyTerm_zero_ball (Z4_4_0Probs_sound ((1,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z4_4_0Probs_sound ((2,0) : PairSlot))) (entropyTerm_zero_ball (Z4_4_0Probs_sound ((2,1) : PairSlot))) Z4_4_0E_2_2_sound Z4_4_0E_2_3_sound (entropyTerm_zero_ball (Z4_4_0Probs_sound ((2,4) : PairSlot))) (entropyTerm_zero_ball (Z4_4_0Probs_sound ((2,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z4_4_0Probs_sound ((3,0) : PairSlot))) (entropyTerm_zero_ball (Z4_4_0Probs_sound ((3,1) : PairSlot))) Z4_4_0E_3_2_sound Z4_4_0E_3_3_sound (entropyTerm_zero_ball (Z4_4_0Probs_sound ((3,4) : PairSlot))) (entropyTerm_zero_ball (Z4_4_0Probs_sound ((3,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z4_4_0Probs_sound ((4,0) : PairSlot))) Z4_4_0E_4_1_sound (entropyTerm_zero_ball (Z4_4_0Probs_sound ((4,2) : PairSlot))) (entropyTerm_zero_ball (Z4_4_0Probs_sound ((4,3) : PairSlot))) (entropyTerm_zero_ball (Z4_4_0Probs_sound ((4,4) : PairSlot))) (entropyTerm_zero_ball (Z4_4_0Probs_sound ((4,5) : PairSlot)))
  · exact forall_fin6 Z4_4_0E_5_0_sound (entropyTerm_zero_ball (Z4_4_0Probs_sound ((5,1) : PairSlot))) (entropyTerm_zero_ball (Z4_4_0Probs_sound ((5,2) : PairSlot))) (entropyTerm_zero_ball (Z4_4_0Probs_sound ((5,3) : PairSlot))) (entropyTerm_zero_ball (Z4_4_0Probs_sound ((5,4) : PairSlot))) (entropyTerm_zero_ball (Z4_4_0Probs_sound ((5,5) : PairSlot)))
lemma Z4_4_0Entropy_sound : Z4_4_0Entropy.Encloses (Foundation.finiteEntropy Z4_4_0Value) := by
  exact contains_sound (entropyPair_enclosed Z4_4_0Value Z4_4_0Terms Z4_4_0Terms_sound) (by decide +kernel)
lemma Z4_4_0Labels_sound : Z4_4_0Labels.Encloses
    (∑ a : PairSlot, (zeroPairLaw (shape 4 4 0) a.1 a.2 : ℝ) *
      Real.log (AllFieldParameters.multiplicity a.1 * AllFieldParameters.multiplicity a.2 : ℕ)) := by
  exact contains_sound (pairSumBall_sound (fun a => .mul (Z4_4_0Probs a) (multLogs a))
    _ (fun a => Ball.mul_sound (Z4_4_0Probs_sound a) (multLogs_sound a))) (by decide +kernel)
lemma Z4_4_0Four_sound_oai : Z4_4_0Four.Encloses (AllFieldZeroLeafRates.fourRate (shape 4 4 0)) := by
  exact contains_sound (Ball.add_sound Z4_4_0Entropy_sound Z4_4_0Labels_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z4_4_0Four_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z4_4_0Four_sound_oai
