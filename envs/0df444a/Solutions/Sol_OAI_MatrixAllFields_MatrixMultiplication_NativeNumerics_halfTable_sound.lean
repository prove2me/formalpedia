-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.halfTable_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T16:00:08.857224+00:00
-- url     : https://prove2.me/submissions/4b780baf-73eb-4fca-a545-54c015816435

import Mathlib
import Definitions.Def_OAIQ254M006
import Definitions.Def_OAIQ254M007
import Definitions.Def_OAIQ254M011
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_inv_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_mul_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkPolynomial_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B1_1_6Half_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B1_2_5Half_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B1_3_4Half_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B1_4_3Half_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B1_5_2Half_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B1_6_1Half_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B2_1_5Half_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B2_2_4Half_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B2_3_3Half_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B2_4_2Half_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B2_5_1Half_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B3_1_4Half_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B3_2_3Half_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B3_3_2Half_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B3_4_1Half_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B4_1_3Half_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B4_2_2Half_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B4_3_1Half_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B5_1_2Half_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B5_2_1Half_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B6_1_1Half_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_Z0_1_7Probs_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_Z0_6_2Probs_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_Z0_7_1Half_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_Z0_8_0Half_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_Z1_7_0Half_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_Z2_0_6Probs_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_Z4_4_0Half_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_Z6_0_2Half_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_Z6_2_0Half_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_Z8_0_0Half_sound

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
lemma w189_sound : w189.Encloses (weight (-2174) : ℝ) := by
  exact weight_enclosed_of_trace (-2174) w189Trace w189S0 w189S1 w189S2 w189S3 w189S4 w189S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

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

lemma Z0_0_8Half_sound (w : Fin 3) (ij : PairSlot) :
    (Z0_0_8Half w ij).Encloses (halfLaw (shape 0 0 8) w ij : ℝ) := by
  have hp : positive (shape 0 0 8) = false := by decide +kernel
  simp only [Z0_0_8Half, halfLaw, hp, Bool.false_eq_true, ite_false, if_false]
  split_ifs
  · exact Ball.exact_sound 1
  · exact Ball.exact_sound 0
  · exact Z0_0_8Probs_sound _
  · exact Z0_0_8Probs_sound _

lemma Z0_1_7Half_sound (w : Fin 3) (ij : PairSlot) :
    (Z0_1_7Half w ij).Encloses (halfLaw (shape 0 1 7) w ij : ℝ) := by
  have hp : positive (shape 0 1 7) = false := by decide +kernel
  simp only [Z0_1_7Half, halfLaw, hp, Bool.false_eq_true, ite_false, if_false]
  split_ifs
  · exact Ball.exact_sound 1
  · exact Ball.exact_sound 0
  · exact Z0_1_7Probs_sound _
  · exact Z0_1_7Probs_sound _

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitB5_1_2
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
lemma w158_sound : w158.Encloses (weight (-6216) : ℝ) := by
  exact weight_enclosed_of_trace (-6216) w158Trace w158S0 w158S1 w158S2 w158S3 w158S4 w158S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w159_sound : w159.Encloses (weight (-6053) : ℝ) := by
  exact weight_enclosed_of_trace (-6053) w159Trace w159S0 w159S1 w159S2 w159S3 w159S4 w159S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w165_sound : w165.Encloses (weight (-5587) : ℝ) := by
  exact weight_enclosed_of_trace (-5587) w165Trace w165S0 w165S1 w165S2 w165S3 w165S4 w165S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w172_sound : w172.Encloses (weight (-4779) : ℝ) := by
  exact weight_enclosed_of_trace (-4779) w172Trace w172S0 w172S1 w172S2 w172S3 w172S4 w172S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

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
lemma w202_sound : w202.Encloses (weight (21564) : ℝ) := by
  exact weight_enclosed_of_trace (21564) w202Trace w202S0 w202S1 w202S2 w202S3 w202S4 w202S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w203_sound : w203.Encloses (weight (21870) : ℝ) := by
  exact weight_enclosed_of_trace (21870) w203Trace w203S0 w203S1 w203S2 w203S3 w203S4 w203S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w205_sound : w205.Encloses (weight (22289) : ℝ) := by
  exact weight_enclosed_of_trace (22289) w205Trace w205S0 w205S1 w205S2 w205S3 w205S4 w205S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w206_sound : w206.Encloses (weight (22299) : ℝ) := by
  exact weight_enclosed_of_trace (22299) w206Trace w206S0 w206S1 w206S2 w206S3 w206S4 w206S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w207_sound : w207.Encloses (weight (22521) : ℝ) := by
  exact weight_enclosed_of_trace (22521) w207Trace w207S0 w207S1 w207S2 w207S3 w207S4 w207S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w209_sound : w209.Encloses (weight (23107) : ℝ) := by
  exact weight_enclosed_of_trace (23107) w209Trace w209S0 w209S1 w209S2 w209S3 w209S4 w209S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w210_sound : w210.Encloses (weight (23786) : ℝ) := by
  exact weight_enclosed_of_trace (23786) w210Trace w210S0 w210S1 w210S2 w210S3 w210S4 w210S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w211_sound : w211.Encloses (weight (23895) : ℝ) := by
  exact weight_enclosed_of_trace (23895) w211Trace w211S0 w211S1 w211S2 w211S3 w211S4 w211S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w213_sound : w213.Encloses (weight (28961) : ℝ) := by
  exact weight_enclosed_of_trace (28961) w213Trace w213S0 w213S1 w213S2 w213S3 w213S4 w213S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w215_sound : w215.Encloses (weight (29263) : ℝ) := by
  exact weight_enclosed_of_trace (29263) w215Trace w215S0 w215S1 w215S2 w215S3 w215S4 w215S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w220_sound : w220.Encloses (weight (43809) : ℝ) := by
  exact weight_enclosed_of_trace (43809) w220Trace w220S0 w220S1 w220S2 w220S3 w220S4 w220S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w222_sound : w222.Encloses (weight (45052) : ℝ) := by
  exact weight_enclosed_of_trace (45052) w222Trace w222S0 w222S1 w222S2 w222S3 w222S4 w222S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
lemma Z0_3_5Raw_sound_0 (j : Fin 6) :
    (Z0_3_5Raw (0,j)).Encloses (weight (orderedPairInteger (shape 0 3 5) 0 j) : ℝ) := by
  fin_cases j
  · change (Z0_3_5Raw (0,0)).Encloses (weight (orderedPairInteger (shape 0 3 5) 0 0) : ℝ)
    have he : orderedPairInteger (shape 0 3 5) 0 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_3_5Raw (0,1)).Encloses (weight (orderedPairInteger (shape 0 3 5) 0 1) : ℝ)
    have he : orderedPairInteger (shape 0 3 5) 0 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_3_5Raw (0,2)).Encloses (weight (orderedPairInteger (shape 0 3 5) 0 2) : ℝ)
    have he : orderedPairInteger (shape 0 3 5) 0 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_3_5Raw (0,3)).Encloses (weight (orderedPairInteger (shape 0 3 5) 0 3) : ℝ)
    have he : orderedPairInteger (shape 0 3 5) 0 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_3_5Raw (0,4)).Encloses (weight (orderedPairInteger (shape 0 3 5) 0 4) : ℝ)
    have he : orderedPairInteger (shape 0 3 5) 0 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_3_5Raw (0,5)).Encloses (weight (orderedPairInteger (shape 0 3 5) 0 5) : ℝ)
    have he : orderedPairInteger (shape 0 3 5) 0 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_3_5Raw_sound_1 (j : Fin 6) :
    (Z0_3_5Raw (1,j)).Encloses (weight (orderedPairInteger (shape 0 3 5) 1 j) : ℝ) := by
  fin_cases j
  · change (Z0_3_5Raw (1,0)).Encloses (weight (orderedPairInteger (shape 0 3 5) 1 0) : ℝ)
    have he : orderedPairInteger (shape 0 3 5) 1 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_3_5Raw (1,1)).Encloses (weight (orderedPairInteger (shape 0 3 5) 1 1) : ℝ)
    have he : orderedPairInteger (shape 0 3 5) 1 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_3_5Raw (1,2)).Encloses (weight (orderedPairInteger (shape 0 3 5) 1 2) : ℝ)
    have he : orderedPairInteger (shape 0 3 5) 1 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_3_5Raw (1,3)).Encloses (weight (orderedPairInteger (shape 0 3 5) 1 3) : ℝ)
    have he : orderedPairInteger (shape 0 3 5) 1 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_3_5Raw (1,4)).Encloses (weight (orderedPairInteger (shape 0 3 5) 1 4) : ℝ)
    have he : orderedPairInteger (shape 0 3 5) 1 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_3_5Raw (1,5)).Encloses (weight (orderedPairInteger (shape 0 3 5) 1 5) : ℝ)
    have he : orderedPairInteger (shape 0 3 5) 1 5 = (-4779) := by decide +kernel
    rw [he]
    exact w172_sound
lemma Z0_3_5Raw_sound_2 (j : Fin 6) :
    (Z0_3_5Raw (2,j)).Encloses (weight (orderedPairInteger (shape 0 3 5) 2 j) : ℝ) := by
  fin_cases j
  · change (Z0_3_5Raw (2,0)).Encloses (weight (orderedPairInteger (shape 0 3 5) 2 0) : ℝ)
    have he : orderedPairInteger (shape 0 3 5) 2 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_3_5Raw (2,1)).Encloses (weight (orderedPairInteger (shape 0 3 5) 2 1) : ℝ)
    have he : orderedPairInteger (shape 0 3 5) 2 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_3_5Raw (2,2)).Encloses (weight (orderedPairInteger (shape 0 3 5) 2 2) : ℝ)
    have he : orderedPairInteger (shape 0 3 5) 2 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_3_5Raw (2,3)).Encloses (weight (orderedPairInteger (shape 0 3 5) 2 3) : ℝ)
    have he : orderedPairInteger (shape 0 3 5) 2 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_3_5Raw (2,4)).Encloses (weight (orderedPairInteger (shape 0 3 5) 2 4) : ℝ)
    have he : orderedPairInteger (shape 0 3 5) 2 4 = (23107) := by decide +kernel
    rw [he]
    exact w209_sound
  · change (Z0_3_5Raw (2,5)).Encloses (weight (orderedPairInteger (shape 0 3 5) 2 5) : ℝ)
    have he : orderedPairInteger (shape 0 3 5) 2 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_3_5Raw_sound_3 (j : Fin 6) :
    (Z0_3_5Raw (3,j)).Encloses (weight (orderedPairInteger (shape 0 3 5) 3 j) : ℝ) := by
  fin_cases j
  · change (Z0_3_5Raw (3,0)).Encloses (weight (orderedPairInteger (shape 0 3 5) 3 0) : ℝ)
    have he : orderedPairInteger (shape 0 3 5) 3 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_3_5Raw (3,1)).Encloses (weight (orderedPairInteger (shape 0 3 5) 3 1) : ℝ)
    have he : orderedPairInteger (shape 0 3 5) 3 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_3_5Raw (3,2)).Encloses (weight (orderedPairInteger (shape 0 3 5) 3 2) : ℝ)
    have he : orderedPairInteger (shape 0 3 5) 3 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_3_5Raw (3,3)).Encloses (weight (orderedPairInteger (shape 0 3 5) 3 3) : ℝ)
    have he : orderedPairInteger (shape 0 3 5) 3 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_3_5Raw (3,4)).Encloses (weight (orderedPairInteger (shape 0 3 5) 3 4) : ℝ)
    have he : orderedPairInteger (shape 0 3 5) 3 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_3_5Raw (3,5)).Encloses (weight (orderedPairInteger (shape 0 3 5) 3 5) : ℝ)
    have he : orderedPairInteger (shape 0 3 5) 3 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_3_5Raw_sound_4 (j : Fin 6) :
    (Z0_3_5Raw (4,j)).Encloses (weight (orderedPairInteger (shape 0 3 5) 4 j) : ℝ) := by
  fin_cases j
  · change (Z0_3_5Raw (4,0)).Encloses (weight (orderedPairInteger (shape 0 3 5) 4 0) : ℝ)
    have he : orderedPairInteger (shape 0 3 5) 4 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_3_5Raw (4,1)).Encloses (weight (orderedPairInteger (shape 0 3 5) 4 1) : ℝ)
    have he : orderedPairInteger (shape 0 3 5) 4 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_3_5Raw (4,2)).Encloses (weight (orderedPairInteger (shape 0 3 5) 4 2) : ℝ)
    have he : orderedPairInteger (shape 0 3 5) 4 2 = (23107) := by decide +kernel
    rw [he]
    exact w209_sound
  · change (Z0_3_5Raw (4,3)).Encloses (weight (orderedPairInteger (shape 0 3 5) 4 3) : ℝ)
    have he : orderedPairInteger (shape 0 3 5) 4 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_3_5Raw (4,4)).Encloses (weight (orderedPairInteger (shape 0 3 5) 4 4) : ℝ)
    have he : orderedPairInteger (shape 0 3 5) 4 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_3_5Raw (4,5)).Encloses (weight (orderedPairInteger (shape 0 3 5) 4 5) : ℝ)
    have he : orderedPairInteger (shape 0 3 5) 4 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_3_5Raw_sound_5 (j : Fin 6) :
    (Z0_3_5Raw (5,j)).Encloses (weight (orderedPairInteger (shape 0 3 5) 5 j) : ℝ) := by
  fin_cases j
  · change (Z0_3_5Raw (5,0)).Encloses (weight (orderedPairInteger (shape 0 3 5) 5 0) : ℝ)
    have he : orderedPairInteger (shape 0 3 5) 5 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_3_5Raw (5,1)).Encloses (weight (orderedPairInteger (shape 0 3 5) 5 1) : ℝ)
    have he : orderedPairInteger (shape 0 3 5) 5 1 = (-4779) := by decide +kernel
    rw [he]
    exact w172_sound
  · change (Z0_3_5Raw (5,2)).Encloses (weight (orderedPairInteger (shape 0 3 5) 5 2) : ℝ)
    have he : orderedPairInteger (shape 0 3 5) 5 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_3_5Raw (5,3)).Encloses (weight (orderedPairInteger (shape 0 3 5) 5 3) : ℝ)
    have he : orderedPairInteger (shape 0 3 5) 5 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_3_5Raw (5,4)).Encloses (weight (orderedPairInteger (shape 0 3 5) 5 4) : ℝ)
    have he : orderedPairInteger (shape 0 3 5) 5 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_3_5Raw (5,5)).Encloses (weight (orderedPairInteger (shape 0 3 5) 5 5) : ℝ)
    have he : orderedPairInteger (shape 0 3 5) 5 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_3_5Raw_sound (ij : PairSlot) :
    (Z0_3_5Raw ij).Encloses (weight (orderedPairInteger (shape 0 3 5) ij.1 ij.2) : ℝ) := by
  rcases ij with ⟨i,j⟩
  revert i
  exact forall_fin6 (Z0_3_5Raw_sound_0 j) (Z0_3_5Raw_sound_1 j) (Z0_3_5Raw_sound_2 j) (Z0_3_5Raw_sound_3 j) (Z0_3_5Raw_sound_4 j) (Z0_3_5Raw_sound_5 j)
lemma Z0_3_5Den_sound : Z0_3_5Den.Encloses
    (((orderedPairs (shape 0 3 5)).map (fun ij => weight (orderedPairInteger (shape 0 3 5) ij.1 ij.2))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (orderedPairs (shape 0 3 5)) Z0_3_5Raw
    (fun ij => weight (orderedPairInteger (shape 0 3 5) ij.1 ij.2))
    (fun ij _ => Z0_3_5Raw_sound ij)) (by decide +kernel)
lemma Z0_3_5Den_pos : 0 < Z0_3_5Den.lower := by decide +kernel
lemma Z0_3_5Contains : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j = shapeMax (shape 0 3 5) →
    contains (.mul (Z0_3_5Raw (i,j)) (.inv Z0_3_5Den)) (Z0_3_5Probs (i,j)) = true := by
  decide +kernel
lemma Z0_3_5Zero : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j ≠ shapeMax (shape 0 3 5) → Z0_3_5Probs (i,j) = .exact 0 := by
  decide +kernel
lemma Z0_3_5Probs_sound (ij : PairSlot) :
    (Z0_3_5Probs ij).Encloses (zeroPairLaw (shape 0 3 5) ij.1 ij.2 : ℝ) := by
  by_cases h : statisticWeight ij.1 + statisticWeight ij.2 = shapeMax (shape 0 3 5)
  · have hb := contains_sound (Ball.mul_sound (Z0_3_5Raw_sound ij)
      (Ball.inv_sound Z0_3_5Den_sound Z0_3_5Den_pos)) (Z0_3_5Contains ij.1 ij.2 h)
    simpa only [zeroPairLaw, h, ite_true, if_true, Rat.cast_div, Rat.cast_mul,
      Rat.cast_inv, div_eq_mul_inv] using hb
  · rw [Z0_3_5Zero ij.1 ij.2 h]
    simpa only [zeroPairLaw, h, ite_false, if_false] using Ball.exact_sound 0

lemma Z0_3_5Half_sound (w : Fin 3) (ij : PairSlot) :
    (Z0_3_5Half w ij).Encloses (halfLaw (shape 0 3 5) w ij : ℝ) := by
  have hp : positive (shape 0 3 5) = false := by decide +kernel
  simp only [Z0_3_5Half, halfLaw, hp, Bool.false_eq_true, ite_false, if_false]
  split_ifs
  · exact Ball.exact_sound 1
  · exact Ball.exact_sound 0
  · exact Z0_3_5Probs_sound _
  · exact Z0_3_5Probs_sound _

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
lemma w121_sound : w121.Encloses (weight (-12831) : ℝ) := by
  exact weight_enclosed_of_trace (-12831) w121Trace w121S0 w121S1 w121S2 w121S3 w121S4 w121S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w122_sound : w122.Encloses (weight (-12708) : ℝ) := by
  exact weight_enclosed_of_trace (-12708) w122Trace w122S0 w122S1 w122S2 w122S3 w122S4 w122S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
lemma Z0_4_4Raw_sound_0 (j : Fin 6) :
    (Z0_4_4Raw (0,j)).Encloses (weight (orderedPairInteger (shape 0 4 4) 0 j) : ℝ) := by
  fin_cases j
  · change (Z0_4_4Raw (0,0)).Encloses (weight (orderedPairInteger (shape 0 4 4) 0 0) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 0 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_4_4Raw (0,1)).Encloses (weight (orderedPairInteger (shape 0 4 4) 0 1) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 0 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_4_4Raw (0,2)).Encloses (weight (orderedPairInteger (shape 0 4 4) 0 2) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 0 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_4_4Raw (0,3)).Encloses (weight (orderedPairInteger (shape 0 4 4) 0 3) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 0 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_4_4Raw (0,4)).Encloses (weight (orderedPairInteger (shape 0 4 4) 0 4) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 0 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_4_4Raw (0,5)).Encloses (weight (orderedPairInteger (shape 0 4 4) 0 5) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 0 5 = (-12831) := by decide +kernel
    rw [he]
    exact w121_sound
lemma Z0_4_4Raw_sound_1 (j : Fin 6) :
    (Z0_4_4Raw (1,j)).Encloses (weight (orderedPairInteger (shape 0 4 4) 1 j) : ℝ) := by
  fin_cases j
  · change (Z0_4_4Raw (1,0)).Encloses (weight (orderedPairInteger (shape 0 4 4) 1 0) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 1 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_4_4Raw (1,1)).Encloses (weight (orderedPairInteger (shape 0 4 4) 1 1) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 1 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_4_4Raw (1,2)).Encloses (weight (orderedPairInteger (shape 0 4 4) 1 2) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 1 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_4_4Raw (1,3)).Encloses (weight (orderedPairInteger (shape 0 4 4) 1 3) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 1 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_4_4Raw (1,4)).Encloses (weight (orderedPairInteger (shape 0 4 4) 1 4) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 1 4 = (29263) := by decide +kernel
    rw [he]
    exact w215_sound
  · change (Z0_4_4Raw (1,5)).Encloses (weight (orderedPairInteger (shape 0 4 4) 1 5) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 1 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_4_4Raw_sound_2 (j : Fin 6) :
    (Z0_4_4Raw (2,j)).Encloses (weight (orderedPairInteger (shape 0 4 4) 2 j) : ℝ) := by
  fin_cases j
  · change (Z0_4_4Raw (2,0)).Encloses (weight (orderedPairInteger (shape 0 4 4) 2 0) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 2 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_4_4Raw (2,1)).Encloses (weight (orderedPairInteger (shape 0 4 4) 2 1) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 2 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_4_4Raw (2,2)).Encloses (weight (orderedPairInteger (shape 0 4 4) 2 2) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 2 2 = (45052) := by decide +kernel
    rw [he]
    exact w222_sound
  · change (Z0_4_4Raw (2,3)).Encloses (weight (orderedPairInteger (shape 0 4 4) 2 3) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 2 3 = (22289) := by decide +kernel
    rw [he]
    exact w205_sound
  · change (Z0_4_4Raw (2,4)).Encloses (weight (orderedPairInteger (shape 0 4 4) 2 4) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 2 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_4_4Raw (2,5)).Encloses (weight (orderedPairInteger (shape 0 4 4) 2 5) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 2 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_4_4Raw_sound_3 (j : Fin 6) :
    (Z0_4_4Raw (3,j)).Encloses (weight (orderedPairInteger (shape 0 4 4) 3 j) : ℝ) := by
  fin_cases j
  · change (Z0_4_4Raw (3,0)).Encloses (weight (orderedPairInteger (shape 0 4 4) 3 0) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 3 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_4_4Raw (3,1)).Encloses (weight (orderedPairInteger (shape 0 4 4) 3 1) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 3 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_4_4Raw (3,2)).Encloses (weight (orderedPairInteger (shape 0 4 4) 3 2) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 3 2 = (22289) := by decide +kernel
    rw [he]
    exact w205_sound
  · change (Z0_4_4Raw (3,3)).Encloses (weight (orderedPairInteger (shape 0 4 4) 3 3) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 3 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_4_4Raw (3,4)).Encloses (weight (orderedPairInteger (shape 0 4 4) 3 4) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 3 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_4_4Raw (3,5)).Encloses (weight (orderedPairInteger (shape 0 4 4) 3 5) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 3 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_4_4Raw_sound_4 (j : Fin 6) :
    (Z0_4_4Raw (4,j)).Encloses (weight (orderedPairInteger (shape 0 4 4) 4 j) : ℝ) := by
  fin_cases j
  · change (Z0_4_4Raw (4,0)).Encloses (weight (orderedPairInteger (shape 0 4 4) 4 0) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 4 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_4_4Raw (4,1)).Encloses (weight (orderedPairInteger (shape 0 4 4) 4 1) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 4 1 = (29263) := by decide +kernel
    rw [he]
    exact w215_sound
  · change (Z0_4_4Raw (4,2)).Encloses (weight (orderedPairInteger (shape 0 4 4) 4 2) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 4 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_4_4Raw (4,3)).Encloses (weight (orderedPairInteger (shape 0 4 4) 4 3) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 4 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_4_4Raw (4,4)).Encloses (weight (orderedPairInteger (shape 0 4 4) 4 4) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 4 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_4_4Raw (4,5)).Encloses (weight (orderedPairInteger (shape 0 4 4) 4 5) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 4 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_4_4Raw_sound_5 (j : Fin 6) :
    (Z0_4_4Raw (5,j)).Encloses (weight (orderedPairInteger (shape 0 4 4) 5 j) : ℝ) := by
  fin_cases j
  · change (Z0_4_4Raw (5,0)).Encloses (weight (orderedPairInteger (shape 0 4 4) 5 0) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 5 0 = (-12831) := by decide +kernel
    rw [he]
    exact w121_sound
  · change (Z0_4_4Raw (5,1)).Encloses (weight (orderedPairInteger (shape 0 4 4) 5 1) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 5 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_4_4Raw (5,2)).Encloses (weight (orderedPairInteger (shape 0 4 4) 5 2) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 5 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_4_4Raw (5,3)).Encloses (weight (orderedPairInteger (shape 0 4 4) 5 3) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 5 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_4_4Raw (5,4)).Encloses (weight (orderedPairInteger (shape 0 4 4) 5 4) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 5 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_4_4Raw (5,5)).Encloses (weight (orderedPairInteger (shape 0 4 4) 5 5) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 5 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_4_4Raw_sound (ij : PairSlot) :
    (Z0_4_4Raw ij).Encloses (weight (orderedPairInteger (shape 0 4 4) ij.1 ij.2) : ℝ) := by
  rcases ij with ⟨i,j⟩
  revert i
  exact forall_fin6 (Z0_4_4Raw_sound_0 j) (Z0_4_4Raw_sound_1 j) (Z0_4_4Raw_sound_2 j) (Z0_4_4Raw_sound_3 j) (Z0_4_4Raw_sound_4 j) (Z0_4_4Raw_sound_5 j)
lemma Z0_4_4Den_sound : Z0_4_4Den.Encloses
    (((orderedPairs (shape 0 4 4)).map (fun ij => weight (orderedPairInteger (shape 0 4 4) ij.1 ij.2))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (orderedPairs (shape 0 4 4)) Z0_4_4Raw
    (fun ij => weight (orderedPairInteger (shape 0 4 4) ij.1 ij.2))
    (fun ij _ => Z0_4_4Raw_sound ij)) (by decide +kernel)
lemma Z0_4_4Den_pos : 0 < Z0_4_4Den.lower := by decide +kernel
lemma Z0_4_4Contains : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j = shapeMax (shape 0 4 4) →
    contains (.mul (Z0_4_4Raw (i,j)) (.inv Z0_4_4Den)) (Z0_4_4Probs (i,j)) = true := by
  decide +kernel
lemma Z0_4_4Zero : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j ≠ shapeMax (shape 0 4 4) → Z0_4_4Probs (i,j) = .exact 0 := by
  decide +kernel
lemma Z0_4_4Probs_sound (ij : PairSlot) :
    (Z0_4_4Probs ij).Encloses (zeroPairLaw (shape 0 4 4) ij.1 ij.2 : ℝ) := by
  by_cases h : statisticWeight ij.1 + statisticWeight ij.2 = shapeMax (shape 0 4 4)
  · have hb := contains_sound (Ball.mul_sound (Z0_4_4Raw_sound ij)
      (Ball.inv_sound Z0_4_4Den_sound Z0_4_4Den_pos)) (Z0_4_4Contains ij.1 ij.2 h)
    simpa only [zeroPairLaw, h, ite_true, if_true, Rat.cast_div, Rat.cast_mul,
      Rat.cast_inv, div_eq_mul_inv] using hb
  · rw [Z0_4_4Zero ij.1 ij.2 h]
    simpa only [zeroPairLaw, h, ite_false, if_false] using Ball.exact_sound 0

lemma Z0_4_4Half_sound (w : Fin 3) (ij : PairSlot) :
    (Z0_4_4Half w ij).Encloses (halfLaw (shape 0 4 4) w ij : ℝ) := by
  have hp : positive (shape 0 4 4) = false := by decide +kernel
  simp only [Z0_4_4Half, halfLaw, hp, Bool.false_eq_true, ite_false, if_false]
  split_ifs
  · exact Ball.exact_sound 1
  · exact Ball.exact_sound 0
  · exact Z0_4_4Probs_sound _
  · exact Z0_4_4Probs_sound _

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Four0_5_3
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
lemma Z0_5_3Raw_sound_0 (j : Fin 6) :
    (Z0_5_3Raw (0,j)).Encloses (weight (orderedPairInteger (shape 0 5 3) 0 j) : ℝ) := by
  fin_cases j
  · change (Z0_5_3Raw (0,0)).Encloses (weight (orderedPairInteger (shape 0 5 3) 0 0) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 0 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (0,1)).Encloses (weight (orderedPairInteger (shape 0 5 3) 0 1) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 0 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (0,2)).Encloses (weight (orderedPairInteger (shape 0 5 3) 0 2) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 0 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (0,3)).Encloses (weight (orderedPairInteger (shape 0 5 3) 0 3) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 0 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (0,4)).Encloses (weight (orderedPairInteger (shape 0 5 3) 0 4) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 0 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (0,5)).Encloses (weight (orderedPairInteger (shape 0 5 3) 0 5) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 0 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_5_3Raw_sound_1 (j : Fin 6) :
    (Z0_5_3Raw (1,j)).Encloses (weight (orderedPairInteger (shape 0 5 3) 1 j) : ℝ) := by
  fin_cases j
  · change (Z0_5_3Raw (1,0)).Encloses (weight (orderedPairInteger (shape 0 5 3) 1 0) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 1 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (1,1)).Encloses (weight (orderedPairInteger (shape 0 5 3) 1 1) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 1 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (1,2)).Encloses (weight (orderedPairInteger (shape 0 5 3) 1 2) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 1 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (1,3)).Encloses (weight (orderedPairInteger (shape 0 5 3) 1 3) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 1 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (1,4)).Encloses (weight (orderedPairInteger (shape 0 5 3) 1 4) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 1 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (1,5)).Encloses (weight (orderedPairInteger (shape 0 5 3) 1 5) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 1 5 = (-6216) := by decide +kernel
    rw [he]
    exact w158_sound
lemma Z0_5_3Raw_sound_2 (j : Fin 6) :
    (Z0_5_3Raw (2,j)).Encloses (weight (orderedPairInteger (shape 0 5 3) 2 j) : ℝ) := by
  fin_cases j
  · change (Z0_5_3Raw (2,0)).Encloses (weight (orderedPairInteger (shape 0 5 3) 2 0) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 2 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (2,1)).Encloses (weight (orderedPairInteger (shape 0 5 3) 2 1) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 2 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (2,2)).Encloses (weight (orderedPairInteger (shape 0 5 3) 2 2) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 2 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (2,3)).Encloses (weight (orderedPairInteger (shape 0 5 3) 2 3) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 2 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (2,4)).Encloses (weight (orderedPairInteger (shape 0 5 3) 2 4) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 2 4 = (23895) := by decide +kernel
    rw [he]
    exact w211_sound
  · change (Z0_5_3Raw (2,5)).Encloses (weight (orderedPairInteger (shape 0 5 3) 2 5) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 2 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_5_3Raw_sound_3 (j : Fin 6) :
    (Z0_5_3Raw (3,j)).Encloses (weight (orderedPairInteger (shape 0 5 3) 3 j) : ℝ) := by
  fin_cases j
  · change (Z0_5_3Raw (3,0)).Encloses (weight (orderedPairInteger (shape 0 5 3) 3 0) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 3 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (3,1)).Encloses (weight (orderedPairInteger (shape 0 5 3) 3 1) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 3 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (3,2)).Encloses (weight (orderedPairInteger (shape 0 5 3) 3 2) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 3 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (3,3)).Encloses (weight (orderedPairInteger (shape 0 5 3) 3 3) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 3 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (3,4)).Encloses (weight (orderedPairInteger (shape 0 5 3) 3 4) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 3 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (3,5)).Encloses (weight (orderedPairInteger (shape 0 5 3) 3 5) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 3 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_5_3Raw_sound_4 (j : Fin 6) :
    (Z0_5_3Raw (4,j)).Encloses (weight (orderedPairInteger (shape 0 5 3) 4 j) : ℝ) := by
  fin_cases j
  · change (Z0_5_3Raw (4,0)).Encloses (weight (orderedPairInteger (shape 0 5 3) 4 0) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 4 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (4,1)).Encloses (weight (orderedPairInteger (shape 0 5 3) 4 1) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 4 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (4,2)).Encloses (weight (orderedPairInteger (shape 0 5 3) 4 2) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 4 2 = (23895) := by decide +kernel
    rw [he]
    exact w211_sound
  · change (Z0_5_3Raw (4,3)).Encloses (weight (orderedPairInteger (shape 0 5 3) 4 3) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 4 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (4,4)).Encloses (weight (orderedPairInteger (shape 0 5 3) 4 4) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 4 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (4,5)).Encloses (weight (orderedPairInteger (shape 0 5 3) 4 5) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 4 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_5_3Raw_sound_5 (j : Fin 6) :
    (Z0_5_3Raw (5,j)).Encloses (weight (orderedPairInteger (shape 0 5 3) 5 j) : ℝ) := by
  fin_cases j
  · change (Z0_5_3Raw (5,0)).Encloses (weight (orderedPairInteger (shape 0 5 3) 5 0) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 5 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (5,1)).Encloses (weight (orderedPairInteger (shape 0 5 3) 5 1) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 5 1 = (-6216) := by decide +kernel
    rw [he]
    exact w158_sound
  · change (Z0_5_3Raw (5,2)).Encloses (weight (orderedPairInteger (shape 0 5 3) 5 2) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 5 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (5,3)).Encloses (weight (orderedPairInteger (shape 0 5 3) 5 3) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 5 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (5,4)).Encloses (weight (orderedPairInteger (shape 0 5 3) 5 4) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 5 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (5,5)).Encloses (weight (orderedPairInteger (shape 0 5 3) 5 5) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 5 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_5_3Raw_sound (ij : PairSlot) :
    (Z0_5_3Raw ij).Encloses (weight (orderedPairInteger (shape 0 5 3) ij.1 ij.2) : ℝ) := by
  rcases ij with ⟨i,j⟩
  revert i
  exact forall_fin6 (Z0_5_3Raw_sound_0 j) (Z0_5_3Raw_sound_1 j) (Z0_5_3Raw_sound_2 j) (Z0_5_3Raw_sound_3 j) (Z0_5_3Raw_sound_4 j) (Z0_5_3Raw_sound_5 j)
lemma Z0_5_3Den_sound : Z0_5_3Den.Encloses
    (((orderedPairs (shape 0 5 3)).map (fun ij => weight (orderedPairInteger (shape 0 5 3) ij.1 ij.2))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (orderedPairs (shape 0 5 3)) Z0_5_3Raw
    (fun ij => weight (orderedPairInteger (shape 0 5 3) ij.1 ij.2))
    (fun ij _ => Z0_5_3Raw_sound ij)) (by decide +kernel)
lemma Z0_5_3Den_pos : 0 < Z0_5_3Den.lower := by decide +kernel
lemma Z0_5_3Contains : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j = shapeMax (shape 0 5 3) →
    contains (.mul (Z0_5_3Raw (i,j)) (.inv Z0_5_3Den)) (Z0_5_3Probs (i,j)) = true := by
  decide +kernel
lemma Z0_5_3Zero : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j ≠ shapeMax (shape 0 5 3) → Z0_5_3Probs (i,j) = .exact 0 := by
  decide +kernel
lemma Z0_5_3Probs_sound (ij : PairSlot) :
    (Z0_5_3Probs ij).Encloses (zeroPairLaw (shape 0 5 3) ij.1 ij.2 : ℝ) := by
  by_cases h : statisticWeight ij.1 + statisticWeight ij.2 = shapeMax (shape 0 5 3)
  · have hb := contains_sound (Ball.mul_sound (Z0_5_3Raw_sound ij)
      (Ball.inv_sound Z0_5_3Den_sound Z0_5_3Den_pos)) (Z0_5_3Contains ij.1 ij.2 h)
    simpa only [zeroPairLaw, h, ite_true, if_true, Rat.cast_div, Rat.cast_mul,
      Rat.cast_inv, div_eq_mul_inv] using hb
  · rw [Z0_5_3Zero ij.1 ij.2 h]
    simpa only [zeroPairLaw, h, ite_false, if_false] using Ball.exact_sound 0

lemma Z0_5_3Half_sound (w : Fin 3) (ij : PairSlot) :
    (Z0_5_3Half w ij).Encloses (halfLaw (shape 0 5 3) w ij : ℝ) := by
  have hp : positive (shape 0 5 3) = false := by decide +kernel
  simp only [Z0_5_3Half, halfLaw, hp, Bool.false_eq_true, ite_false, if_false]
  split_ifs
  · exact Ball.exact_sound 1
  · exact Ball.exact_sound 0
  · exact Z0_5_3Probs_sound _
  · exact Z0_5_3Probs_sound _

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Four1_0_7
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

lemma Z1_0_7Half_sound (w : Fin 3) (ij : PairSlot) :
    (Z1_0_7Half w ij).Encloses (halfLaw (shape 1 0 7) w ij : ℝ) := by
  have hp : positive (shape 1 0 7) = false := by decide +kernel
  simp only [Z1_0_7Half, halfLaw, hp, Bool.false_eq_true, ite_false, if_false]
  split_ifs
  · exact Ball.exact_sound 1
  · exact Ball.exact_sound 0
  · exact Z1_0_7Probs_sound _
  · exact Z1_0_7Probs_sound _

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

namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
lemma Z0_6_2Half_sound (w : Fin 3) (ij : PairSlot) :
    (Z0_6_2Half w ij).Encloses (halfLaw (shape 0 6 2) w ij : ℝ) := by
  have hp : positive (shape 0 6 2) = false := by decide +kernel
  simp only [Z0_6_2Half, halfLaw, hp, Bool.false_eq_true, ite_false, if_false]
  split_ifs
  · exact Ball.exact_sound 1
  · exact Ball.exact_sound 0
  · exact Z0_6_2Probs_sound _
  · exact Z0_6_2Probs_sound _

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitA1_3_12
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

lemma w132_sound : w132.Encloses (weight (-9766) : ℝ) := by
  exact weight_enclosed_of_trace (-9766) w132Trace w132S0 w132S1 w132S2 w132S3 w132S4 w132S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w139_sound : w139.Encloses (weight (-7811) : ℝ) := by
  exact weight_enclosed_of_trace (-7811) w139Trace w139S0 w139S1 w139S2 w139S3 w139S4 w139S5
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

lemma Z0_2_6Half_sound (w : Fin 3) (ij : PairSlot) :
    (Z0_2_6Half w ij).Encloses (halfLaw (shape 0 2 6) w ij : ℝ) := by
  have hp : positive (shape 0 2 6) = false := by decide +kernel
  simp only [Z0_2_6Half, halfLaw, hp, Bool.false_eq_true, ite_false, if_false]
  split_ifs
  · exact Ball.exact_sound 1
  · exact Ball.exact_sound 0
  · exact Z0_2_6Probs_sound _
  · exact Z0_2_6Probs_sound _

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Four2_0_6
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
lemma Z2_0_6Half_sound (w : Fin 3) (ij : PairSlot) :
    (Z2_0_6Half w ij).Encloses (halfLaw (shape 2 0 6) w ij : ℝ) := by
  have hp : positive (shape 2 0 6) = false := by decide +kernel
  simp only [Z2_0_6Half, halfLaw, hp, Bool.false_eq_true, ite_false, if_false]
  split_ifs
  · exact Ball.exact_sound 1
  · exact Ball.exact_sound 0
  · exact Z2_0_6Probs_sound _
  · exact Z2_0_6Probs_sound _

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Four2_6_0
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

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Four3_0_5
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
lemma Z3_0_5Raw_sound_0 (j : Fin 6) :
    (Z3_0_5Raw (0,j)).Encloses (weight (orderedPairInteger (shape 3 0 5) 0 j) : ℝ) := by
  fin_cases j
  · change (Z3_0_5Raw (0,0)).Encloses (weight (orderedPairInteger (shape 3 0 5) 0 0) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 0 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (0,1)).Encloses (weight (orderedPairInteger (shape 3 0 5) 0 1) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 0 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (0,2)).Encloses (weight (orderedPairInteger (shape 3 0 5) 0 2) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 0 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (0,3)).Encloses (weight (orderedPairInteger (shape 3 0 5) 0 3) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 0 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (0,4)).Encloses (weight (orderedPairInteger (shape 3 0 5) 0 4) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 0 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (0,5)).Encloses (weight (orderedPairInteger (shape 3 0 5) 0 5) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 0 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z3_0_5Raw_sound_1 (j : Fin 6) :
    (Z3_0_5Raw (1,j)).Encloses (weight (orderedPairInteger (shape 3 0 5) 1 j) : ℝ) := by
  fin_cases j
  · change (Z3_0_5Raw (1,0)).Encloses (weight (orderedPairInteger (shape 3 0 5) 1 0) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 1 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (1,1)).Encloses (weight (orderedPairInteger (shape 3 0 5) 1 1) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 1 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (1,2)).Encloses (weight (orderedPairInteger (shape 3 0 5) 1 2) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 1 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (1,3)).Encloses (weight (orderedPairInteger (shape 3 0 5) 1 3) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 1 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (1,4)).Encloses (weight (orderedPairInteger (shape 3 0 5) 1 4) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 1 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (1,5)).Encloses (weight (orderedPairInteger (shape 3 0 5) 1 5) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 1 5 = (-2174) := by decide +kernel
    rw [he]
    exact w189_sound
lemma Z3_0_5Raw_sound_2 (j : Fin 6) :
    (Z3_0_5Raw (2,j)).Encloses (weight (orderedPairInteger (shape 3 0 5) 2 j) : ℝ) := by
  fin_cases j
  · change (Z3_0_5Raw (2,0)).Encloses (weight (orderedPairInteger (shape 3 0 5) 2 0) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 2 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (2,1)).Encloses (weight (orderedPairInteger (shape 3 0 5) 2 1) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 2 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (2,2)).Encloses (weight (orderedPairInteger (shape 3 0 5) 2 2) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 2 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (2,3)).Encloses (weight (orderedPairInteger (shape 3 0 5) 2 3) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 2 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (2,4)).Encloses (weight (orderedPairInteger (shape 3 0 5) 2 4) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 2 4 = (21564) := by decide +kernel
    rw [he]
    exact w202_sound
  · change (Z3_0_5Raw (2,5)).Encloses (weight (orderedPairInteger (shape 3 0 5) 2 5) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 2 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z3_0_5Raw_sound_3 (j : Fin 6) :
    (Z3_0_5Raw (3,j)).Encloses (weight (orderedPairInteger (shape 3 0 5) 3 j) : ℝ) := by
  fin_cases j
  · change (Z3_0_5Raw (3,0)).Encloses (weight (orderedPairInteger (shape 3 0 5) 3 0) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 3 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (3,1)).Encloses (weight (orderedPairInteger (shape 3 0 5) 3 1) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 3 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (3,2)).Encloses (weight (orderedPairInteger (shape 3 0 5) 3 2) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 3 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (3,3)).Encloses (weight (orderedPairInteger (shape 3 0 5) 3 3) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 3 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (3,4)).Encloses (weight (orderedPairInteger (shape 3 0 5) 3 4) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 3 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (3,5)).Encloses (weight (orderedPairInteger (shape 3 0 5) 3 5) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 3 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z3_0_5Raw_sound_4 (j : Fin 6) :
    (Z3_0_5Raw (4,j)).Encloses (weight (orderedPairInteger (shape 3 0 5) 4 j) : ℝ) := by
  fin_cases j
  · change (Z3_0_5Raw (4,0)).Encloses (weight (orderedPairInteger (shape 3 0 5) 4 0) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 4 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (4,1)).Encloses (weight (orderedPairInteger (shape 3 0 5) 4 1) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 4 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (4,2)).Encloses (weight (orderedPairInteger (shape 3 0 5) 4 2) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 4 2 = (21564) := by decide +kernel
    rw [he]
    exact w202_sound
  · change (Z3_0_5Raw (4,3)).Encloses (weight (orderedPairInteger (shape 3 0 5) 4 3) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 4 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (4,4)).Encloses (weight (orderedPairInteger (shape 3 0 5) 4 4) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 4 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (4,5)).Encloses (weight (orderedPairInteger (shape 3 0 5) 4 5) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 4 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z3_0_5Raw_sound_5 (j : Fin 6) :
    (Z3_0_5Raw (5,j)).Encloses (weight (orderedPairInteger (shape 3 0 5) 5 j) : ℝ) := by
  fin_cases j
  · change (Z3_0_5Raw (5,0)).Encloses (weight (orderedPairInteger (shape 3 0 5) 5 0) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 5 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (5,1)).Encloses (weight (orderedPairInteger (shape 3 0 5) 5 1) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 5 1 = (-2174) := by decide +kernel
    rw [he]
    exact w189_sound
  · change (Z3_0_5Raw (5,2)).Encloses (weight (orderedPairInteger (shape 3 0 5) 5 2) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 5 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (5,3)).Encloses (weight (orderedPairInteger (shape 3 0 5) 5 3) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 5 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (5,4)).Encloses (weight (orderedPairInteger (shape 3 0 5) 5 4) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 5 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (5,5)).Encloses (weight (orderedPairInteger (shape 3 0 5) 5 5) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 5 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z3_0_5Raw_sound (ij : PairSlot) :
    (Z3_0_5Raw ij).Encloses (weight (orderedPairInteger (shape 3 0 5) ij.1 ij.2) : ℝ) := by
  rcases ij with ⟨i,j⟩
  revert i
  exact forall_fin6 (Z3_0_5Raw_sound_0 j) (Z3_0_5Raw_sound_1 j) (Z3_0_5Raw_sound_2 j) (Z3_0_5Raw_sound_3 j) (Z3_0_5Raw_sound_4 j) (Z3_0_5Raw_sound_5 j)
lemma Z3_0_5Den_sound : Z3_0_5Den.Encloses
    (((orderedPairs (shape 3 0 5)).map (fun ij => weight (orderedPairInteger (shape 3 0 5) ij.1 ij.2))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (orderedPairs (shape 3 0 5)) Z3_0_5Raw
    (fun ij => weight (orderedPairInteger (shape 3 0 5) ij.1 ij.2))
    (fun ij _ => Z3_0_5Raw_sound ij)) (by decide +kernel)
lemma Z3_0_5Den_pos : 0 < Z3_0_5Den.lower := by decide +kernel
lemma Z3_0_5Contains : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j = shapeMax (shape 3 0 5) →
    contains (.mul (Z3_0_5Raw (i,j)) (.inv Z3_0_5Den)) (Z3_0_5Probs (i,j)) = true := by
  decide +kernel
lemma Z3_0_5Zero : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j ≠ shapeMax (shape 3 0 5) → Z3_0_5Probs (i,j) = .exact 0 := by
  decide +kernel
lemma Z3_0_5Probs_sound (ij : PairSlot) :
    (Z3_0_5Probs ij).Encloses (zeroPairLaw (shape 3 0 5) ij.1 ij.2 : ℝ) := by
  by_cases h : statisticWeight ij.1 + statisticWeight ij.2 = shapeMax (shape 3 0 5)
  · have hb := contains_sound (Ball.mul_sound (Z3_0_5Raw_sound ij)
      (Ball.inv_sound Z3_0_5Den_sound Z3_0_5Den_pos)) (Z3_0_5Contains ij.1 ij.2 h)
    simpa only [zeroPairLaw, h, ite_true, if_true, Rat.cast_div, Rat.cast_mul,
      Rat.cast_inv, div_eq_mul_inv] using hb
  · rw [Z3_0_5Zero ij.1 ij.2 h]
    simpa only [zeroPairLaw, h, ite_false, if_false] using Ball.exact_sound 0

lemma Z3_0_5Half_sound (w : Fin 3) (ij : PairSlot) :
    (Z3_0_5Half w ij).Encloses (halfLaw (shape 3 0 5) w ij : ℝ) := by
  have hp : positive (shape 3 0 5) = false := by decide +kernel
  simp only [Z3_0_5Half, halfLaw, hp, Bool.false_eq_true, ite_false, if_false]
  split_ifs
  · exact Ball.exact_sound 1
  · exact Ball.exact_sound 0
  · exact Z3_0_5Probs_sound _
  · exact Z3_0_5Probs_sound _

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Four3_5_0
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
lemma Z3_5_0Raw_sound_0 (j : Fin 6) :
    (Z3_5_0Raw (0,j)).Encloses (weight (orderedPairInteger (shape 3 5 0) 0 j) : ℝ) := by
  fin_cases j
  · change (Z3_5_0Raw (0,0)).Encloses (weight (orderedPairInteger (shape 3 5 0) 0 0) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 0 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_5_0Raw (0,1)).Encloses (weight (orderedPairInteger (shape 3 5 0) 0 1) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 0 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_5_0Raw (0,2)).Encloses (weight (orderedPairInteger (shape 3 5 0) 0 2) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 0 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_5_0Raw (0,3)).Encloses (weight (orderedPairInteger (shape 3 5 0) 0 3) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 0 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_5_0Raw (0,4)).Encloses (weight (orderedPairInteger (shape 3 5 0) 0 4) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 0 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_5_0Raw (0,5)).Encloses (weight (orderedPairInteger (shape 3 5 0) 0 5) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 0 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z3_5_0Raw_sound_1 (j : Fin 6) :
    (Z3_5_0Raw (1,j)).Encloses (weight (orderedPairInteger (shape 3 5 0) 1 j) : ℝ) := by
  fin_cases j
  · change (Z3_5_0Raw (1,0)).Encloses (weight (orderedPairInteger (shape 3 5 0) 1 0) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 1 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_5_0Raw (1,1)).Encloses (weight (orderedPairInteger (shape 3 5 0) 1 1) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 1 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_5_0Raw (1,2)).Encloses (weight (orderedPairInteger (shape 3 5 0) 1 2) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 1 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_5_0Raw (1,3)).Encloses (weight (orderedPairInteger (shape 3 5 0) 1 3) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 1 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_5_0Raw (1,4)).Encloses (weight (orderedPairInteger (shape 3 5 0) 1 4) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 1 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_5_0Raw (1,5)).Encloses (weight (orderedPairInteger (shape 3 5 0) 1 5) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 1 5 = (-5587) := by decide +kernel
    rw [he]
    exact w165_sound
lemma Z3_5_0Raw_sound_2 (j : Fin 6) :
    (Z3_5_0Raw (2,j)).Encloses (weight (orderedPairInteger (shape 3 5 0) 2 j) : ℝ) := by
  fin_cases j
  · change (Z3_5_0Raw (2,0)).Encloses (weight (orderedPairInteger (shape 3 5 0) 2 0) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 2 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_5_0Raw (2,1)).Encloses (weight (orderedPairInteger (shape 3 5 0) 2 1) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 2 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_5_0Raw (2,2)).Encloses (weight (orderedPairInteger (shape 3 5 0) 2 2) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 2 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_5_0Raw (2,3)).Encloses (weight (orderedPairInteger (shape 3 5 0) 2 3) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 2 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_5_0Raw (2,4)).Encloses (weight (orderedPairInteger (shape 3 5 0) 2 4) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 2 4 = (22521) := by decide +kernel
    rw [he]
    exact w207_sound
  · change (Z3_5_0Raw (2,5)).Encloses (weight (orderedPairInteger (shape 3 5 0) 2 5) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 2 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z3_5_0Raw_sound_3 (j : Fin 6) :
    (Z3_5_0Raw (3,j)).Encloses (weight (orderedPairInteger (shape 3 5 0) 3 j) : ℝ) := by
  fin_cases j
  · change (Z3_5_0Raw (3,0)).Encloses (weight (orderedPairInteger (shape 3 5 0) 3 0) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 3 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_5_0Raw (3,1)).Encloses (weight (orderedPairInteger (shape 3 5 0) 3 1) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 3 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_5_0Raw (3,2)).Encloses (weight (orderedPairInteger (shape 3 5 0) 3 2) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 3 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_5_0Raw (3,3)).Encloses (weight (orderedPairInteger (shape 3 5 0) 3 3) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 3 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_5_0Raw (3,4)).Encloses (weight (orderedPairInteger (shape 3 5 0) 3 4) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 3 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_5_0Raw (3,5)).Encloses (weight (orderedPairInteger (shape 3 5 0) 3 5) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 3 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z3_5_0Raw_sound_4 (j : Fin 6) :
    (Z3_5_0Raw (4,j)).Encloses (weight (orderedPairInteger (shape 3 5 0) 4 j) : ℝ) := by
  fin_cases j
  · change (Z3_5_0Raw (4,0)).Encloses (weight (orderedPairInteger (shape 3 5 0) 4 0) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 4 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_5_0Raw (4,1)).Encloses (weight (orderedPairInteger (shape 3 5 0) 4 1) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 4 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_5_0Raw (4,2)).Encloses (weight (orderedPairInteger (shape 3 5 0) 4 2) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 4 2 = (22521) := by decide +kernel
    rw [he]
    exact w207_sound
  · change (Z3_5_0Raw (4,3)).Encloses (weight (orderedPairInteger (shape 3 5 0) 4 3) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 4 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_5_0Raw (4,4)).Encloses (weight (orderedPairInteger (shape 3 5 0) 4 4) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 4 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_5_0Raw (4,5)).Encloses (weight (orderedPairInteger (shape 3 5 0) 4 5) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 4 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z3_5_0Raw_sound_5 (j : Fin 6) :
    (Z3_5_0Raw (5,j)).Encloses (weight (orderedPairInteger (shape 3 5 0) 5 j) : ℝ) := by
  fin_cases j
  · change (Z3_5_0Raw (5,0)).Encloses (weight (orderedPairInteger (shape 3 5 0) 5 0) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 5 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_5_0Raw (5,1)).Encloses (weight (orderedPairInteger (shape 3 5 0) 5 1) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 5 1 = (-5587) := by decide +kernel
    rw [he]
    exact w165_sound
  · change (Z3_5_0Raw (5,2)).Encloses (weight (orderedPairInteger (shape 3 5 0) 5 2) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 5 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_5_0Raw (5,3)).Encloses (weight (orderedPairInteger (shape 3 5 0) 5 3) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 5 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_5_0Raw (5,4)).Encloses (weight (orderedPairInteger (shape 3 5 0) 5 4) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 5 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_5_0Raw (5,5)).Encloses (weight (orderedPairInteger (shape 3 5 0) 5 5) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 5 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z3_5_0Raw_sound (ij : PairSlot) :
    (Z3_5_0Raw ij).Encloses (weight (orderedPairInteger (shape 3 5 0) ij.1 ij.2) : ℝ) := by
  rcases ij with ⟨i,j⟩
  revert i
  exact forall_fin6 (Z3_5_0Raw_sound_0 j) (Z3_5_0Raw_sound_1 j) (Z3_5_0Raw_sound_2 j) (Z3_5_0Raw_sound_3 j) (Z3_5_0Raw_sound_4 j) (Z3_5_0Raw_sound_5 j)
lemma Z3_5_0Den_sound : Z3_5_0Den.Encloses
    (((orderedPairs (shape 3 5 0)).map (fun ij => weight (orderedPairInteger (shape 3 5 0) ij.1 ij.2))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (orderedPairs (shape 3 5 0)) Z3_5_0Raw
    (fun ij => weight (orderedPairInteger (shape 3 5 0) ij.1 ij.2))
    (fun ij _ => Z3_5_0Raw_sound ij)) (by decide +kernel)
lemma Z3_5_0Den_pos : 0 < Z3_5_0Den.lower := by decide +kernel
lemma Z3_5_0Contains : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j = shapeMax (shape 3 5 0) →
    contains (.mul (Z3_5_0Raw (i,j)) (.inv Z3_5_0Den)) (Z3_5_0Probs (i,j)) = true := by
  decide +kernel
lemma Z3_5_0Zero : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j ≠ shapeMax (shape 3 5 0) → Z3_5_0Probs (i,j) = .exact 0 := by
  decide +kernel
lemma Z3_5_0Probs_sound (ij : PairSlot) :
    (Z3_5_0Probs ij).Encloses (zeroPairLaw (shape 3 5 0) ij.1 ij.2 : ℝ) := by
  by_cases h : statisticWeight ij.1 + statisticWeight ij.2 = shapeMax (shape 3 5 0)
  · have hb := contains_sound (Ball.mul_sound (Z3_5_0Raw_sound ij)
      (Ball.inv_sound Z3_5_0Den_sound Z3_5_0Den_pos)) (Z3_5_0Contains ij.1 ij.2 h)
    simpa only [zeroPairLaw, h, ite_true, if_true, Rat.cast_div, Rat.cast_mul,
      Rat.cast_inv, div_eq_mul_inv] using hb
  · rw [Z3_5_0Zero ij.1 ij.2 h]
    simpa only [zeroPairLaw, h, ite_false, if_false] using Ball.exact_sound 0

lemma Z3_5_0Half_sound (w : Fin 3) (ij : PairSlot) :
    (Z3_5_0Half w ij).Encloses (halfLaw (shape 3 5 0) w ij : ℝ) := by
  have hp : positive (shape 3 5 0) = false := by decide +kernel
  simp only [Z3_5_0Half, halfLaw, hp, Bool.false_eq_true, ite_false, if_false]
  split_ifs
  · exact Ball.exact_sound 1
  · exact Ball.exact_sound 0
  · exact Z3_5_0Probs_sound _
  · exact Z3_5_0Probs_sound _

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Four4_0_4
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
lemma Z4_0_4Raw_sound_0 (j : Fin 6) :
    (Z4_0_4Raw (0,j)).Encloses (weight (orderedPairInteger (shape 4 0 4) 0 j) : ℝ) := by
  fin_cases j
  · change (Z4_0_4Raw (0,0)).Encloses (weight (orderedPairInteger (shape 4 0 4) 0 0) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 0 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_0_4Raw (0,1)).Encloses (weight (orderedPairInteger (shape 4 0 4) 0 1) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 0 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_0_4Raw (0,2)).Encloses (weight (orderedPairInteger (shape 4 0 4) 0 2) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 0 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_0_4Raw (0,3)).Encloses (weight (orderedPairInteger (shape 4 0 4) 0 3) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 0 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_0_4Raw (0,4)).Encloses (weight (orderedPairInteger (shape 4 0 4) 0 4) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 0 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_0_4Raw (0,5)).Encloses (weight (orderedPairInteger (shape 4 0 4) 0 5) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 0 5 = (-9766) := by decide +kernel
    rw [he]
    exact w132_sound
lemma Z4_0_4Raw_sound_1 (j : Fin 6) :
    (Z4_0_4Raw (1,j)).Encloses (weight (orderedPairInteger (shape 4 0 4) 1 j) : ℝ) := by
  fin_cases j
  · change (Z4_0_4Raw (1,0)).Encloses (weight (orderedPairInteger (shape 4 0 4) 1 0) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 1 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_0_4Raw (1,1)).Encloses (weight (orderedPairInteger (shape 4 0 4) 1 1) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 1 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_0_4Raw (1,2)).Encloses (weight (orderedPairInteger (shape 4 0 4) 1 2) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 1 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_0_4Raw (1,3)).Encloses (weight (orderedPairInteger (shape 4 0 4) 1 3) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 1 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_0_4Raw (1,4)).Encloses (weight (orderedPairInteger (shape 4 0 4) 1 4) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 1 4 = (28961) := by decide +kernel
    rw [he]
    exact w213_sound
  · change (Z4_0_4Raw (1,5)).Encloses (weight (orderedPairInteger (shape 4 0 4) 1 5) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 1 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z4_0_4Raw_sound_2 (j : Fin 6) :
    (Z4_0_4Raw (2,j)).Encloses (weight (orderedPairInteger (shape 4 0 4) 2 j) : ℝ) := by
  fin_cases j
  · change (Z4_0_4Raw (2,0)).Encloses (weight (orderedPairInteger (shape 4 0 4) 2 0) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 2 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_0_4Raw (2,1)).Encloses (weight (orderedPairInteger (shape 4 0 4) 2 1) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 2 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_0_4Raw (2,2)).Encloses (weight (orderedPairInteger (shape 4 0 4) 2 2) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 2 2 = (43809) := by decide +kernel
    rw [he]
    exact w220_sound
  · change (Z4_0_4Raw (2,3)).Encloses (weight (orderedPairInteger (shape 4 0 4) 2 3) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 2 3 = (22299) := by decide +kernel
    rw [he]
    exact w206_sound
  · change (Z4_0_4Raw (2,4)).Encloses (weight (orderedPairInteger (shape 4 0 4) 2 4) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 2 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_0_4Raw (2,5)).Encloses (weight (orderedPairInteger (shape 4 0 4) 2 5) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 2 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z4_0_4Raw_sound_3 (j : Fin 6) :
    (Z4_0_4Raw (3,j)).Encloses (weight (orderedPairInteger (shape 4 0 4) 3 j) : ℝ) := by
  fin_cases j
  · change (Z4_0_4Raw (3,0)).Encloses (weight (orderedPairInteger (shape 4 0 4) 3 0) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 3 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_0_4Raw (3,1)).Encloses (weight (orderedPairInteger (shape 4 0 4) 3 1) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 3 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_0_4Raw (3,2)).Encloses (weight (orderedPairInteger (shape 4 0 4) 3 2) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 3 2 = (22299) := by decide +kernel
    rw [he]
    exact w206_sound
  · change (Z4_0_4Raw (3,3)).Encloses (weight (orderedPairInteger (shape 4 0 4) 3 3) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 3 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_0_4Raw (3,4)).Encloses (weight (orderedPairInteger (shape 4 0 4) 3 4) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 3 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_0_4Raw (3,5)).Encloses (weight (orderedPairInteger (shape 4 0 4) 3 5) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 3 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z4_0_4Raw_sound_4 (j : Fin 6) :
    (Z4_0_4Raw (4,j)).Encloses (weight (orderedPairInteger (shape 4 0 4) 4 j) : ℝ) := by
  fin_cases j
  · change (Z4_0_4Raw (4,0)).Encloses (weight (orderedPairInteger (shape 4 0 4) 4 0) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 4 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_0_4Raw (4,1)).Encloses (weight (orderedPairInteger (shape 4 0 4) 4 1) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 4 1 = (28961) := by decide +kernel
    rw [he]
    exact w213_sound
  · change (Z4_0_4Raw (4,2)).Encloses (weight (orderedPairInteger (shape 4 0 4) 4 2) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 4 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_0_4Raw (4,3)).Encloses (weight (orderedPairInteger (shape 4 0 4) 4 3) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 4 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_0_4Raw (4,4)).Encloses (weight (orderedPairInteger (shape 4 0 4) 4 4) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 4 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_0_4Raw (4,5)).Encloses (weight (orderedPairInteger (shape 4 0 4) 4 5) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 4 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z4_0_4Raw_sound_5 (j : Fin 6) :
    (Z4_0_4Raw (5,j)).Encloses (weight (orderedPairInteger (shape 4 0 4) 5 j) : ℝ) := by
  fin_cases j
  · change (Z4_0_4Raw (5,0)).Encloses (weight (orderedPairInteger (shape 4 0 4) 5 0) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 5 0 = (-9766) := by decide +kernel
    rw [he]
    exact w132_sound
  · change (Z4_0_4Raw (5,1)).Encloses (weight (orderedPairInteger (shape 4 0 4) 5 1) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 5 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_0_4Raw (5,2)).Encloses (weight (orderedPairInteger (shape 4 0 4) 5 2) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 5 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_0_4Raw (5,3)).Encloses (weight (orderedPairInteger (shape 4 0 4) 5 3) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 5 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_0_4Raw (5,4)).Encloses (weight (orderedPairInteger (shape 4 0 4) 5 4) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 5 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_0_4Raw (5,5)).Encloses (weight (orderedPairInteger (shape 4 0 4) 5 5) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 5 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z4_0_4Raw_sound (ij : PairSlot) :
    (Z4_0_4Raw ij).Encloses (weight (orderedPairInteger (shape 4 0 4) ij.1 ij.2) : ℝ) := by
  rcases ij with ⟨i,j⟩
  revert i
  exact forall_fin6 (Z4_0_4Raw_sound_0 j) (Z4_0_4Raw_sound_1 j) (Z4_0_4Raw_sound_2 j) (Z4_0_4Raw_sound_3 j) (Z4_0_4Raw_sound_4 j) (Z4_0_4Raw_sound_5 j)
lemma Z4_0_4Den_sound : Z4_0_4Den.Encloses
    (((orderedPairs (shape 4 0 4)).map (fun ij => weight (orderedPairInteger (shape 4 0 4) ij.1 ij.2))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (orderedPairs (shape 4 0 4)) Z4_0_4Raw
    (fun ij => weight (orderedPairInteger (shape 4 0 4) ij.1 ij.2))
    (fun ij _ => Z4_0_4Raw_sound ij)) (by decide +kernel)
lemma Z4_0_4Den_pos : 0 < Z4_0_4Den.lower := by decide +kernel
lemma Z4_0_4Contains : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j = shapeMax (shape 4 0 4) →
    contains (.mul (Z4_0_4Raw (i,j)) (.inv Z4_0_4Den)) (Z4_0_4Probs (i,j)) = true := by
  decide +kernel
lemma Z4_0_4Zero : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j ≠ shapeMax (shape 4 0 4) → Z4_0_4Probs (i,j) = .exact 0 := by
  decide +kernel
lemma Z4_0_4Probs_sound (ij : PairSlot) :
    (Z4_0_4Probs ij).Encloses (zeroPairLaw (shape 4 0 4) ij.1 ij.2 : ℝ) := by
  by_cases h : statisticWeight ij.1 + statisticWeight ij.2 = shapeMax (shape 4 0 4)
  · have hb := contains_sound (Ball.mul_sound (Z4_0_4Raw_sound ij)
      (Ball.inv_sound Z4_0_4Den_sound Z4_0_4Den_pos)) (Z4_0_4Contains ij.1 ij.2 h)
    simpa only [zeroPairLaw, h, ite_true, if_true, Rat.cast_div, Rat.cast_mul,
      Rat.cast_inv, div_eq_mul_inv] using hb
  · rw [Z4_0_4Zero ij.1 ij.2 h]
    simpa only [zeroPairLaw, h, ite_false, if_false] using Ball.exact_sound 0

lemma Z4_0_4Half_sound (w : Fin 3) (ij : PairSlot) :
    (Z4_0_4Half w ij).Encloses (halfLaw (shape 4 0 4) w ij : ℝ) := by
  have hp : positive (shape 4 0 4) = false := by decide +kernel
  simp only [Z4_0_4Half, halfLaw, hp, Bool.false_eq_true, ite_false, if_false]
  split_ifs
  · exact Ball.exact_sound 1
  · exact Ball.exact_sound 0
  · exact Z4_0_4Probs_sound _
  · exact Z4_0_4Probs_sound _

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Four5_0_3
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
lemma Z5_0_3Raw_sound_0 (j : Fin 6) :
    (Z5_0_3Raw (0,j)).Encloses (weight (orderedPairInteger (shape 5 0 3) 0 j) : ℝ) := by
  fin_cases j
  · change (Z5_0_3Raw (0,0)).Encloses (weight (orderedPairInteger (shape 5 0 3) 0 0) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 0 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_0_3Raw (0,1)).Encloses (weight (orderedPairInteger (shape 5 0 3) 0 1) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 0 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_0_3Raw (0,2)).Encloses (weight (orderedPairInteger (shape 5 0 3) 0 2) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 0 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_0_3Raw (0,3)).Encloses (weight (orderedPairInteger (shape 5 0 3) 0 3) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 0 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_0_3Raw (0,4)).Encloses (weight (orderedPairInteger (shape 5 0 3) 0 4) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 0 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_0_3Raw (0,5)).Encloses (weight (orderedPairInteger (shape 5 0 3) 0 5) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 0 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z5_0_3Raw_sound_1 (j : Fin 6) :
    (Z5_0_3Raw (1,j)).Encloses (weight (orderedPairInteger (shape 5 0 3) 1 j) : ℝ) := by
  fin_cases j
  · change (Z5_0_3Raw (1,0)).Encloses (weight (orderedPairInteger (shape 5 0 3) 1 0) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 1 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_0_3Raw (1,1)).Encloses (weight (orderedPairInteger (shape 5 0 3) 1 1) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 1 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_0_3Raw (1,2)).Encloses (weight (orderedPairInteger (shape 5 0 3) 1 2) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 1 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_0_3Raw (1,3)).Encloses (weight (orderedPairInteger (shape 5 0 3) 1 3) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 1 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_0_3Raw (1,4)).Encloses (weight (orderedPairInteger (shape 5 0 3) 1 4) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 1 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_0_3Raw (1,5)).Encloses (weight (orderedPairInteger (shape 5 0 3) 1 5) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 1 5 = (-7811) := by decide +kernel
    rw [he]
    exact w139_sound
lemma Z5_0_3Raw_sound_2 (j : Fin 6) :
    (Z5_0_3Raw (2,j)).Encloses (weight (orderedPairInteger (shape 5 0 3) 2 j) : ℝ) := by
  fin_cases j
  · change (Z5_0_3Raw (2,0)).Encloses (weight (orderedPairInteger (shape 5 0 3) 2 0) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 2 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_0_3Raw (2,1)).Encloses (weight (orderedPairInteger (shape 5 0 3) 2 1) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 2 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_0_3Raw (2,2)).Encloses (weight (orderedPairInteger (shape 5 0 3) 2 2) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 2 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_0_3Raw (2,3)).Encloses (weight (orderedPairInteger (shape 5 0 3) 2 3) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 2 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_0_3Raw (2,4)).Encloses (weight (orderedPairInteger (shape 5 0 3) 2 4) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 2 4 = (21870) := by decide +kernel
    rw [he]
    exact w203_sound
  · change (Z5_0_3Raw (2,5)).Encloses (weight (orderedPairInteger (shape 5 0 3) 2 5) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 2 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z5_0_3Raw_sound_3 (j : Fin 6) :
    (Z5_0_3Raw (3,j)).Encloses (weight (orderedPairInteger (shape 5 0 3) 3 j) : ℝ) := by
  fin_cases j
  · change (Z5_0_3Raw (3,0)).Encloses (weight (orderedPairInteger (shape 5 0 3) 3 0) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 3 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_0_3Raw (3,1)).Encloses (weight (orderedPairInteger (shape 5 0 3) 3 1) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 3 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_0_3Raw (3,2)).Encloses (weight (orderedPairInteger (shape 5 0 3) 3 2) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 3 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_0_3Raw (3,3)).Encloses (weight (orderedPairInteger (shape 5 0 3) 3 3) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 3 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_0_3Raw (3,4)).Encloses (weight (orderedPairInteger (shape 5 0 3) 3 4) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 3 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_0_3Raw (3,5)).Encloses (weight (orderedPairInteger (shape 5 0 3) 3 5) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 3 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z5_0_3Raw_sound_4 (j : Fin 6) :
    (Z5_0_3Raw (4,j)).Encloses (weight (orderedPairInteger (shape 5 0 3) 4 j) : ℝ) := by
  fin_cases j
  · change (Z5_0_3Raw (4,0)).Encloses (weight (orderedPairInteger (shape 5 0 3) 4 0) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 4 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_0_3Raw (4,1)).Encloses (weight (orderedPairInteger (shape 5 0 3) 4 1) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 4 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_0_3Raw (4,2)).Encloses (weight (orderedPairInteger (shape 5 0 3) 4 2) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 4 2 = (21870) := by decide +kernel
    rw [he]
    exact w203_sound
  · change (Z5_0_3Raw (4,3)).Encloses (weight (orderedPairInteger (shape 5 0 3) 4 3) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 4 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_0_3Raw (4,4)).Encloses (weight (orderedPairInteger (shape 5 0 3) 4 4) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 4 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_0_3Raw (4,5)).Encloses (weight (orderedPairInteger (shape 5 0 3) 4 5) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 4 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z5_0_3Raw_sound_5 (j : Fin 6) :
    (Z5_0_3Raw (5,j)).Encloses (weight (orderedPairInteger (shape 5 0 3) 5 j) : ℝ) := by
  fin_cases j
  · change (Z5_0_3Raw (5,0)).Encloses (weight (orderedPairInteger (shape 5 0 3) 5 0) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 5 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_0_3Raw (5,1)).Encloses (weight (orderedPairInteger (shape 5 0 3) 5 1) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 5 1 = (-7811) := by decide +kernel
    rw [he]
    exact w139_sound
  · change (Z5_0_3Raw (5,2)).Encloses (weight (orderedPairInteger (shape 5 0 3) 5 2) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 5 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_0_3Raw (5,3)).Encloses (weight (orderedPairInteger (shape 5 0 3) 5 3) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 5 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_0_3Raw (5,4)).Encloses (weight (orderedPairInteger (shape 5 0 3) 5 4) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 5 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_0_3Raw (5,5)).Encloses (weight (orderedPairInteger (shape 5 0 3) 5 5) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 5 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z5_0_3Raw_sound (ij : PairSlot) :
    (Z5_0_3Raw ij).Encloses (weight (orderedPairInteger (shape 5 0 3) ij.1 ij.2) : ℝ) := by
  rcases ij with ⟨i,j⟩
  revert i
  exact forall_fin6 (Z5_0_3Raw_sound_0 j) (Z5_0_3Raw_sound_1 j) (Z5_0_3Raw_sound_2 j) (Z5_0_3Raw_sound_3 j) (Z5_0_3Raw_sound_4 j) (Z5_0_3Raw_sound_5 j)
lemma Z5_0_3Den_sound : Z5_0_3Den.Encloses
    (((orderedPairs (shape 5 0 3)).map (fun ij => weight (orderedPairInteger (shape 5 0 3) ij.1 ij.2))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (orderedPairs (shape 5 0 3)) Z5_0_3Raw
    (fun ij => weight (orderedPairInteger (shape 5 0 3) ij.1 ij.2))
    (fun ij _ => Z5_0_3Raw_sound ij)) (by decide +kernel)
lemma Z5_0_3Den_pos : 0 < Z5_0_3Den.lower := by decide +kernel
lemma Z5_0_3Contains : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j = shapeMax (shape 5 0 3) →
    contains (.mul (Z5_0_3Raw (i,j)) (.inv Z5_0_3Den)) (Z5_0_3Probs (i,j)) = true := by
  decide +kernel
lemma Z5_0_3Zero : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j ≠ shapeMax (shape 5 0 3) → Z5_0_3Probs (i,j) = .exact 0 := by
  decide +kernel
lemma Z5_0_3Probs_sound (ij : PairSlot) :
    (Z5_0_3Probs ij).Encloses (zeroPairLaw (shape 5 0 3) ij.1 ij.2 : ℝ) := by
  by_cases h : statisticWeight ij.1 + statisticWeight ij.2 = shapeMax (shape 5 0 3)
  · have hb := contains_sound (Ball.mul_sound (Z5_0_3Raw_sound ij)
      (Ball.inv_sound Z5_0_3Den_sound Z5_0_3Den_pos)) (Z5_0_3Contains ij.1 ij.2 h)
    simpa only [zeroPairLaw, h, ite_true, if_true, Rat.cast_div, Rat.cast_mul,
      Rat.cast_inv, div_eq_mul_inv] using hb
  · rw [Z5_0_3Zero ij.1 ij.2 h]
    simpa only [zeroPairLaw, h, ite_false, if_false] using Ball.exact_sound 0

lemma Z5_0_3Half_sound (w : Fin 3) (ij : PairSlot) :
    (Z5_0_3Half w ij).Encloses (halfLaw (shape 5 0 3) w ij : ℝ) := by
  have hp : positive (shape 5 0 3) = false := by decide +kernel
  simp only [Z5_0_3Half, halfLaw, hp, Bool.false_eq_true, ite_false, if_false]
  split_ifs
  · exact Ball.exact_sound 1
  · exact Ball.exact_sound 0
  · exact Z5_0_3Probs_sound _
  · exact Z5_0_3Probs_sound _

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Four5_3_0
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
lemma Z5_3_0Raw_sound_0 (j : Fin 6) :
    (Z5_3_0Raw (0,j)).Encloses (weight (orderedPairInteger (shape 5 3 0) 0 j) : ℝ) := by
  fin_cases j
  · change (Z5_3_0Raw (0,0)).Encloses (weight (orderedPairInteger (shape 5 3 0) 0 0) : ℝ)
    have he : orderedPairInteger (shape 5 3 0) 0 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_3_0Raw (0,1)).Encloses (weight (orderedPairInteger (shape 5 3 0) 0 1) : ℝ)
    have he : orderedPairInteger (shape 5 3 0) 0 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_3_0Raw (0,2)).Encloses (weight (orderedPairInteger (shape 5 3 0) 0 2) : ℝ)
    have he : orderedPairInteger (shape 5 3 0) 0 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_3_0Raw (0,3)).Encloses (weight (orderedPairInteger (shape 5 3 0) 0 3) : ℝ)
    have he : orderedPairInteger (shape 5 3 0) 0 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_3_0Raw (0,4)).Encloses (weight (orderedPairInteger (shape 5 3 0) 0 4) : ℝ)
    have he : orderedPairInteger (shape 5 3 0) 0 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_3_0Raw (0,5)).Encloses (weight (orderedPairInteger (shape 5 3 0) 0 5) : ℝ)
    have he : orderedPairInteger (shape 5 3 0) 0 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z5_3_0Raw_sound_1 (j : Fin 6) :
    (Z5_3_0Raw (1,j)).Encloses (weight (orderedPairInteger (shape 5 3 0) 1 j) : ℝ) := by
  fin_cases j
  · change (Z5_3_0Raw (1,0)).Encloses (weight (orderedPairInteger (shape 5 3 0) 1 0) : ℝ)
    have he : orderedPairInteger (shape 5 3 0) 1 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_3_0Raw (1,1)).Encloses (weight (orderedPairInteger (shape 5 3 0) 1 1) : ℝ)
    have he : orderedPairInteger (shape 5 3 0) 1 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_3_0Raw (1,2)).Encloses (weight (orderedPairInteger (shape 5 3 0) 1 2) : ℝ)
    have he : orderedPairInteger (shape 5 3 0) 1 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_3_0Raw (1,3)).Encloses (weight (orderedPairInteger (shape 5 3 0) 1 3) : ℝ)
    have he : orderedPairInteger (shape 5 3 0) 1 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_3_0Raw (1,4)).Encloses (weight (orderedPairInteger (shape 5 3 0) 1 4) : ℝ)
    have he : orderedPairInteger (shape 5 3 0) 1 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_3_0Raw (1,5)).Encloses (weight (orderedPairInteger (shape 5 3 0) 1 5) : ℝ)
    have he : orderedPairInteger (shape 5 3 0) 1 5 = (-6053) := by decide +kernel
    rw [he]
    exact w159_sound
lemma Z5_3_0Raw_sound_2 (j : Fin 6) :
    (Z5_3_0Raw (2,j)).Encloses (weight (orderedPairInteger (shape 5 3 0) 2 j) : ℝ) := by
  fin_cases j
  · change (Z5_3_0Raw (2,0)).Encloses (weight (orderedPairInteger (shape 5 3 0) 2 0) : ℝ)
    have he : orderedPairInteger (shape 5 3 0) 2 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_3_0Raw (2,1)).Encloses (weight (orderedPairInteger (shape 5 3 0) 2 1) : ℝ)
    have he : orderedPairInteger (shape 5 3 0) 2 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_3_0Raw (2,2)).Encloses (weight (orderedPairInteger (shape 5 3 0) 2 2) : ℝ)
    have he : orderedPairInteger (shape 5 3 0) 2 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_3_0Raw (2,3)).Encloses (weight (orderedPairInteger (shape 5 3 0) 2 3) : ℝ)
    have he : orderedPairInteger (shape 5 3 0) 2 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_3_0Raw (2,4)).Encloses (weight (orderedPairInteger (shape 5 3 0) 2 4) : ℝ)
    have he : orderedPairInteger (shape 5 3 0) 2 4 = (23786) := by decide +kernel
    rw [he]
    exact w210_sound
  · change (Z5_3_0Raw (2,5)).Encloses (weight (orderedPairInteger (shape 5 3 0) 2 5) : ℝ)
    have he : orderedPairInteger (shape 5 3 0) 2 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z5_3_0Raw_sound_3 (j : Fin 6) :
    (Z5_3_0Raw (3,j)).Encloses (weight (orderedPairInteger (shape 5 3 0) 3 j) : ℝ) := by
  fin_cases j
  · change (Z5_3_0Raw (3,0)).Encloses (weight (orderedPairInteger (shape 5 3 0) 3 0) : ℝ)
    have he : orderedPairInteger (shape 5 3 0) 3 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_3_0Raw (3,1)).Encloses (weight (orderedPairInteger (shape 5 3 0) 3 1) : ℝ)
    have he : orderedPairInteger (shape 5 3 0) 3 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_3_0Raw (3,2)).Encloses (weight (orderedPairInteger (shape 5 3 0) 3 2) : ℝ)
    have he : orderedPairInteger (shape 5 3 0) 3 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_3_0Raw (3,3)).Encloses (weight (orderedPairInteger (shape 5 3 0) 3 3) : ℝ)
    have he : orderedPairInteger (shape 5 3 0) 3 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_3_0Raw (3,4)).Encloses (weight (orderedPairInteger (shape 5 3 0) 3 4) : ℝ)
    have he : orderedPairInteger (shape 5 3 0) 3 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_3_0Raw (3,5)).Encloses (weight (orderedPairInteger (shape 5 3 0) 3 5) : ℝ)
    have he : orderedPairInteger (shape 5 3 0) 3 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z5_3_0Raw_sound_4 (j : Fin 6) :
    (Z5_3_0Raw (4,j)).Encloses (weight (orderedPairInteger (shape 5 3 0) 4 j) : ℝ) := by
  fin_cases j
  · change (Z5_3_0Raw (4,0)).Encloses (weight (orderedPairInteger (shape 5 3 0) 4 0) : ℝ)
    have he : orderedPairInteger (shape 5 3 0) 4 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_3_0Raw (4,1)).Encloses (weight (orderedPairInteger (shape 5 3 0) 4 1) : ℝ)
    have he : orderedPairInteger (shape 5 3 0) 4 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_3_0Raw (4,2)).Encloses (weight (orderedPairInteger (shape 5 3 0) 4 2) : ℝ)
    have he : orderedPairInteger (shape 5 3 0) 4 2 = (23786) := by decide +kernel
    rw [he]
    exact w210_sound
  · change (Z5_3_0Raw (4,3)).Encloses (weight (orderedPairInteger (shape 5 3 0) 4 3) : ℝ)
    have he : orderedPairInteger (shape 5 3 0) 4 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_3_0Raw (4,4)).Encloses (weight (orderedPairInteger (shape 5 3 0) 4 4) : ℝ)
    have he : orderedPairInteger (shape 5 3 0) 4 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_3_0Raw (4,5)).Encloses (weight (orderedPairInteger (shape 5 3 0) 4 5) : ℝ)
    have he : orderedPairInteger (shape 5 3 0) 4 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z5_3_0Raw_sound_5 (j : Fin 6) :
    (Z5_3_0Raw (5,j)).Encloses (weight (orderedPairInteger (shape 5 3 0) 5 j) : ℝ) := by
  fin_cases j
  · change (Z5_3_0Raw (5,0)).Encloses (weight (orderedPairInteger (shape 5 3 0) 5 0) : ℝ)
    have he : orderedPairInteger (shape 5 3 0) 5 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_3_0Raw (5,1)).Encloses (weight (orderedPairInteger (shape 5 3 0) 5 1) : ℝ)
    have he : orderedPairInteger (shape 5 3 0) 5 1 = (-6053) := by decide +kernel
    rw [he]
    exact w159_sound
  · change (Z5_3_0Raw (5,2)).Encloses (weight (orderedPairInteger (shape 5 3 0) 5 2) : ℝ)
    have he : orderedPairInteger (shape 5 3 0) 5 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_3_0Raw (5,3)).Encloses (weight (orderedPairInteger (shape 5 3 0) 5 3) : ℝ)
    have he : orderedPairInteger (shape 5 3 0) 5 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_3_0Raw (5,4)).Encloses (weight (orderedPairInteger (shape 5 3 0) 5 4) : ℝ)
    have he : orderedPairInteger (shape 5 3 0) 5 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_3_0Raw (5,5)).Encloses (weight (orderedPairInteger (shape 5 3 0) 5 5) : ℝ)
    have he : orderedPairInteger (shape 5 3 0) 5 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z5_3_0Raw_sound (ij : PairSlot) :
    (Z5_3_0Raw ij).Encloses (weight (orderedPairInteger (shape 5 3 0) ij.1 ij.2) : ℝ) := by
  rcases ij with ⟨i,j⟩
  revert i
  exact forall_fin6 (Z5_3_0Raw_sound_0 j) (Z5_3_0Raw_sound_1 j) (Z5_3_0Raw_sound_2 j) (Z5_3_0Raw_sound_3 j) (Z5_3_0Raw_sound_4 j) (Z5_3_0Raw_sound_5 j)
lemma Z5_3_0Den_sound : Z5_3_0Den.Encloses
    (((orderedPairs (shape 5 3 0)).map (fun ij => weight (orderedPairInteger (shape 5 3 0) ij.1 ij.2))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (orderedPairs (shape 5 3 0)) Z5_3_0Raw
    (fun ij => weight (orderedPairInteger (shape 5 3 0) ij.1 ij.2))
    (fun ij _ => Z5_3_0Raw_sound ij)) (by decide +kernel)
lemma Z5_3_0Den_pos : 0 < Z5_3_0Den.lower := by decide +kernel
lemma Z5_3_0Contains : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j = shapeMax (shape 5 3 0) →
    contains (.mul (Z5_3_0Raw (i,j)) (.inv Z5_3_0Den)) (Z5_3_0Probs (i,j)) = true := by
  decide +kernel
lemma Z5_3_0Zero : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j ≠ shapeMax (shape 5 3 0) → Z5_3_0Probs (i,j) = .exact 0 := by
  decide +kernel
lemma Z5_3_0Probs_sound (ij : PairSlot) :
    (Z5_3_0Probs ij).Encloses (zeroPairLaw (shape 5 3 0) ij.1 ij.2 : ℝ) := by
  by_cases h : statisticWeight ij.1 + statisticWeight ij.2 = shapeMax (shape 5 3 0)
  · have hb := contains_sound (Ball.mul_sound (Z5_3_0Raw_sound ij)
      (Ball.inv_sound Z5_3_0Den_sound Z5_3_0Den_pos)) (Z5_3_0Contains ij.1 ij.2 h)
    simpa only [zeroPairLaw, h, ite_true, if_true, Rat.cast_div, Rat.cast_mul,
      Rat.cast_inv, div_eq_mul_inv] using hb
  · rw [Z5_3_0Zero ij.1 ij.2 h]
    simpa only [zeroPairLaw, h, ite_false, if_false] using Ball.exact_sound 0

lemma Z5_3_0Half_sound (w : Fin 3) (ij : PairSlot) :
    (Z5_3_0Half w ij).Encloses (halfLaw (shape 5 3 0) w ij : ℝ) := by
  have hp : positive (shape 5 3 0) = false := by decide +kernel
  simp only [Z5_3_0Half, halfLaw, hp, Bool.false_eq_true, ite_false, if_false]
  split_ifs
  · exact Ball.exact_sound 1
  · exact Ball.exact_sound 0
  · exact Z5_3_0Probs_sound _
  · exact Z5_3_0Probs_sound _

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Four7_0_1
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
lemma Z7_0_1Raw_sound_0 (j : Fin 6) :
    (Z7_0_1Raw (0,j)).Encloses (weight (orderedPairInteger (shape 7 0 1) 0 j) : ℝ) := by
  fin_cases j
  · change (Z7_0_1Raw (0,0)).Encloses (weight (orderedPairInteger (shape 7 0 1) 0 0) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 0 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (0,1)).Encloses (weight (orderedPairInteger (shape 7 0 1) 0 1) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 0 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (0,2)).Encloses (weight (orderedPairInteger (shape 7 0 1) 0 2) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 0 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (0,3)).Encloses (weight (orderedPairInteger (shape 7 0 1) 0 3) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 0 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (0,4)).Encloses (weight (orderedPairInteger (shape 7 0 1) 0 4) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 0 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (0,5)).Encloses (weight (orderedPairInteger (shape 7 0 1) 0 5) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 0 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z7_0_1Raw_sound_1 (j : Fin 6) :
    (Z7_0_1Raw (1,j)).Encloses (weight (orderedPairInteger (shape 7 0 1) 1 j) : ℝ) := by
  fin_cases j
  · change (Z7_0_1Raw (1,0)).Encloses (weight (orderedPairInteger (shape 7 0 1) 1 0) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 1 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (1,1)).Encloses (weight (orderedPairInteger (shape 7 0 1) 1 1) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 1 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (1,2)).Encloses (weight (orderedPairInteger (shape 7 0 1) 1 2) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 1 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (1,3)).Encloses (weight (orderedPairInteger (shape 7 0 1) 1 3) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 1 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (1,4)).Encloses (weight (orderedPairInteger (shape 7 0 1) 1 4) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 1 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (1,5)).Encloses (weight (orderedPairInteger (shape 7 0 1) 1 5) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 1 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z7_0_1Raw_sound_2 (j : Fin 6) :
    (Z7_0_1Raw (2,j)).Encloses (weight (orderedPairInteger (shape 7 0 1) 2 j) : ℝ) := by
  fin_cases j
  · change (Z7_0_1Raw (2,0)).Encloses (weight (orderedPairInteger (shape 7 0 1) 2 0) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 2 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (2,1)).Encloses (weight (orderedPairInteger (shape 7 0 1) 2 1) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 2 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (2,2)).Encloses (weight (orderedPairInteger (shape 7 0 1) 2 2) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 2 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (2,3)).Encloses (weight (orderedPairInteger (shape 7 0 1) 2 3) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 2 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (2,4)).Encloses (weight (orderedPairInteger (shape 7 0 1) 2 4) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 2 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (2,5)).Encloses (weight (orderedPairInteger (shape 7 0 1) 2 5) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 2 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z7_0_1Raw_sound_3 (j : Fin 6) :
    (Z7_0_1Raw (3,j)).Encloses (weight (orderedPairInteger (shape 7 0 1) 3 j) : ℝ) := by
  fin_cases j
  · change (Z7_0_1Raw (3,0)).Encloses (weight (orderedPairInteger (shape 7 0 1) 3 0) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 3 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (3,1)).Encloses (weight (orderedPairInteger (shape 7 0 1) 3 1) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 3 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (3,2)).Encloses (weight (orderedPairInteger (shape 7 0 1) 3 2) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 3 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (3,3)).Encloses (weight (orderedPairInteger (shape 7 0 1) 3 3) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 3 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (3,4)).Encloses (weight (orderedPairInteger (shape 7 0 1) 3 4) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 3 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (3,5)).Encloses (weight (orderedPairInteger (shape 7 0 1) 3 5) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 3 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z7_0_1Raw_sound_4 (j : Fin 6) :
    (Z7_0_1Raw (4,j)).Encloses (weight (orderedPairInteger (shape 7 0 1) 4 j) : ℝ) := by
  fin_cases j
  · change (Z7_0_1Raw (4,0)).Encloses (weight (orderedPairInteger (shape 7 0 1) 4 0) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 4 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (4,1)).Encloses (weight (orderedPairInteger (shape 7 0 1) 4 1) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 4 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (4,2)).Encloses (weight (orderedPairInteger (shape 7 0 1) 4 2) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 4 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (4,3)).Encloses (weight (orderedPairInteger (shape 7 0 1) 4 3) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 4 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (4,4)).Encloses (weight (orderedPairInteger (shape 7 0 1) 4 4) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 4 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (4,5)).Encloses (weight (orderedPairInteger (shape 7 0 1) 4 5) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 4 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z7_0_1Raw_sound_5 (j : Fin 6) :
    (Z7_0_1Raw (5,j)).Encloses (weight (orderedPairInteger (shape 7 0 1) 5 j) : ℝ) := by
  fin_cases j
  · change (Z7_0_1Raw (5,0)).Encloses (weight (orderedPairInteger (shape 7 0 1) 5 0) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 5 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (5,1)).Encloses (weight (orderedPairInteger (shape 7 0 1) 5 1) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 5 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (5,2)).Encloses (weight (orderedPairInteger (shape 7 0 1) 5 2) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 5 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (5,3)).Encloses (weight (orderedPairInteger (shape 7 0 1) 5 3) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 5 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (5,4)).Encloses (weight (orderedPairInteger (shape 7 0 1) 5 4) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 5 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (5,5)).Encloses (weight (orderedPairInteger (shape 7 0 1) 5 5) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 5 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z7_0_1Raw_sound (ij : PairSlot) :
    (Z7_0_1Raw ij).Encloses (weight (orderedPairInteger (shape 7 0 1) ij.1 ij.2) : ℝ) := by
  rcases ij with ⟨i,j⟩
  revert i
  exact forall_fin6 (Z7_0_1Raw_sound_0 j) (Z7_0_1Raw_sound_1 j) (Z7_0_1Raw_sound_2 j) (Z7_0_1Raw_sound_3 j) (Z7_0_1Raw_sound_4 j) (Z7_0_1Raw_sound_5 j)
lemma Z7_0_1Den_sound : Z7_0_1Den.Encloses
    (((orderedPairs (shape 7 0 1)).map (fun ij => weight (orderedPairInteger (shape 7 0 1) ij.1 ij.2))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (orderedPairs (shape 7 0 1)) Z7_0_1Raw
    (fun ij => weight (orderedPairInteger (shape 7 0 1) ij.1 ij.2))
    (fun ij _ => Z7_0_1Raw_sound ij)) (by decide +kernel)
lemma Z7_0_1Den_pos : 0 < Z7_0_1Den.lower := by decide +kernel
lemma Z7_0_1Contains : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j = shapeMax (shape 7 0 1) →
    contains (.mul (Z7_0_1Raw (i,j)) (.inv Z7_0_1Den)) (Z7_0_1Probs (i,j)) = true := by
  decide +kernel
lemma Z7_0_1Zero : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j ≠ shapeMax (shape 7 0 1) → Z7_0_1Probs (i,j) = .exact 0 := by
  decide +kernel
lemma Z7_0_1Probs_sound (ij : PairSlot) :
    (Z7_0_1Probs ij).Encloses (zeroPairLaw (shape 7 0 1) ij.1 ij.2 : ℝ) := by
  by_cases h : statisticWeight ij.1 + statisticWeight ij.2 = shapeMax (shape 7 0 1)
  · have hb := contains_sound (Ball.mul_sound (Z7_0_1Raw_sound ij)
      (Ball.inv_sound Z7_0_1Den_sound Z7_0_1Den_pos)) (Z7_0_1Contains ij.1 ij.2 h)
    simpa only [zeroPairLaw, h, ite_true, if_true, Rat.cast_div, Rat.cast_mul,
      Rat.cast_inv, div_eq_mul_inv] using hb
  · rw [Z7_0_1Zero ij.1 ij.2 h]
    simpa only [zeroPairLaw, h, ite_false, if_false] using Ball.exact_sound 0

lemma Z7_0_1Half_sound (w : Fin 3) (ij : PairSlot) :
    (Z7_0_1Half w ij).Encloses (halfLaw (shape 7 0 1) w ij : ℝ) := by
  have hp : positive (shape 7 0 1) = false := by decide +kernel
  simp only [Z7_0_1Half, halfLaw, hp, Bool.false_eq_true, ite_false, if_false]
  split_ifs
  · exact Ball.exact_sound 1
  · exact Ball.exact_sound 0
  · exact Z7_0_1Probs_sound _
  · exact Z7_0_1Probs_sound _

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Four7_1_0
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
lemma Z7_1_0Raw_sound_0 (j : Fin 6) :
    (Z7_1_0Raw (0,j)).Encloses (weight (orderedPairInteger (shape 7 1 0) 0 j) : ℝ) := by
  fin_cases j
  · change (Z7_1_0Raw (0,0)).Encloses (weight (orderedPairInteger (shape 7 1 0) 0 0) : ℝ)
    have he : orderedPairInteger (shape 7 1 0) 0 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_1_0Raw (0,1)).Encloses (weight (orderedPairInteger (shape 7 1 0) 0 1) : ℝ)
    have he : orderedPairInteger (shape 7 1 0) 0 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_1_0Raw (0,2)).Encloses (weight (orderedPairInteger (shape 7 1 0) 0 2) : ℝ)
    have he : orderedPairInteger (shape 7 1 0) 0 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_1_0Raw (0,3)).Encloses (weight (orderedPairInteger (shape 7 1 0) 0 3) : ℝ)
    have he : orderedPairInteger (shape 7 1 0) 0 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_1_0Raw (0,4)).Encloses (weight (orderedPairInteger (shape 7 1 0) 0 4) : ℝ)
    have he : orderedPairInteger (shape 7 1 0) 0 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_1_0Raw (0,5)).Encloses (weight (orderedPairInteger (shape 7 1 0) 0 5) : ℝ)
    have he : orderedPairInteger (shape 7 1 0) 0 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z7_1_0Raw_sound_1 (j : Fin 6) :
    (Z7_1_0Raw (1,j)).Encloses (weight (orderedPairInteger (shape 7 1 0) 1 j) : ℝ) := by
  fin_cases j
  · change (Z7_1_0Raw (1,0)).Encloses (weight (orderedPairInteger (shape 7 1 0) 1 0) : ℝ)
    have he : orderedPairInteger (shape 7 1 0) 1 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_1_0Raw (1,1)).Encloses (weight (orderedPairInteger (shape 7 1 0) 1 1) : ℝ)
    have he : orderedPairInteger (shape 7 1 0) 1 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_1_0Raw (1,2)).Encloses (weight (orderedPairInteger (shape 7 1 0) 1 2) : ℝ)
    have he : orderedPairInteger (shape 7 1 0) 1 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_1_0Raw (1,3)).Encloses (weight (orderedPairInteger (shape 7 1 0) 1 3) : ℝ)
    have he : orderedPairInteger (shape 7 1 0) 1 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_1_0Raw (1,4)).Encloses (weight (orderedPairInteger (shape 7 1 0) 1 4) : ℝ)
    have he : orderedPairInteger (shape 7 1 0) 1 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_1_0Raw (1,5)).Encloses (weight (orderedPairInteger (shape 7 1 0) 1 5) : ℝ)
    have he : orderedPairInteger (shape 7 1 0) 1 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z7_1_0Raw_sound_2 (j : Fin 6) :
    (Z7_1_0Raw (2,j)).Encloses (weight (orderedPairInteger (shape 7 1 0) 2 j) : ℝ) := by
  fin_cases j
  · change (Z7_1_0Raw (2,0)).Encloses (weight (orderedPairInteger (shape 7 1 0) 2 0) : ℝ)
    have he : orderedPairInteger (shape 7 1 0) 2 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_1_0Raw (2,1)).Encloses (weight (orderedPairInteger (shape 7 1 0) 2 1) : ℝ)
    have he : orderedPairInteger (shape 7 1 0) 2 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_1_0Raw (2,2)).Encloses (weight (orderedPairInteger (shape 7 1 0) 2 2) : ℝ)
    have he : orderedPairInteger (shape 7 1 0) 2 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_1_0Raw (2,3)).Encloses (weight (orderedPairInteger (shape 7 1 0) 2 3) : ℝ)
    have he : orderedPairInteger (shape 7 1 0) 2 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_1_0Raw (2,4)).Encloses (weight (orderedPairInteger (shape 7 1 0) 2 4) : ℝ)
    have he : orderedPairInteger (shape 7 1 0) 2 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_1_0Raw (2,5)).Encloses (weight (orderedPairInteger (shape 7 1 0) 2 5) : ℝ)
    have he : orderedPairInteger (shape 7 1 0) 2 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z7_1_0Raw_sound_3 (j : Fin 6) :
    (Z7_1_0Raw (3,j)).Encloses (weight (orderedPairInteger (shape 7 1 0) 3 j) : ℝ) := by
  fin_cases j
  · change (Z7_1_0Raw (3,0)).Encloses (weight (orderedPairInteger (shape 7 1 0) 3 0) : ℝ)
    have he : orderedPairInteger (shape 7 1 0) 3 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_1_0Raw (3,1)).Encloses (weight (orderedPairInteger (shape 7 1 0) 3 1) : ℝ)
    have he : orderedPairInteger (shape 7 1 0) 3 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_1_0Raw (3,2)).Encloses (weight (orderedPairInteger (shape 7 1 0) 3 2) : ℝ)
    have he : orderedPairInteger (shape 7 1 0) 3 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_1_0Raw (3,3)).Encloses (weight (orderedPairInteger (shape 7 1 0) 3 3) : ℝ)
    have he : orderedPairInteger (shape 7 1 0) 3 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_1_0Raw (3,4)).Encloses (weight (orderedPairInteger (shape 7 1 0) 3 4) : ℝ)
    have he : orderedPairInteger (shape 7 1 0) 3 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_1_0Raw (3,5)).Encloses (weight (orderedPairInteger (shape 7 1 0) 3 5) : ℝ)
    have he : orderedPairInteger (shape 7 1 0) 3 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z7_1_0Raw_sound_4 (j : Fin 6) :
    (Z7_1_0Raw (4,j)).Encloses (weight (orderedPairInteger (shape 7 1 0) 4 j) : ℝ) := by
  fin_cases j
  · change (Z7_1_0Raw (4,0)).Encloses (weight (orderedPairInteger (shape 7 1 0) 4 0) : ℝ)
    have he : orderedPairInteger (shape 7 1 0) 4 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_1_0Raw (4,1)).Encloses (weight (orderedPairInteger (shape 7 1 0) 4 1) : ℝ)
    have he : orderedPairInteger (shape 7 1 0) 4 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_1_0Raw (4,2)).Encloses (weight (orderedPairInteger (shape 7 1 0) 4 2) : ℝ)
    have he : orderedPairInteger (shape 7 1 0) 4 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_1_0Raw (4,3)).Encloses (weight (orderedPairInteger (shape 7 1 0) 4 3) : ℝ)
    have he : orderedPairInteger (shape 7 1 0) 4 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_1_0Raw (4,4)).Encloses (weight (orderedPairInteger (shape 7 1 0) 4 4) : ℝ)
    have he : orderedPairInteger (shape 7 1 0) 4 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_1_0Raw (4,5)).Encloses (weight (orderedPairInteger (shape 7 1 0) 4 5) : ℝ)
    have he : orderedPairInteger (shape 7 1 0) 4 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z7_1_0Raw_sound_5 (j : Fin 6) :
    (Z7_1_0Raw (5,j)).Encloses (weight (orderedPairInteger (shape 7 1 0) 5 j) : ℝ) := by
  fin_cases j
  · change (Z7_1_0Raw (5,0)).Encloses (weight (orderedPairInteger (shape 7 1 0) 5 0) : ℝ)
    have he : orderedPairInteger (shape 7 1 0) 5 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_1_0Raw (5,1)).Encloses (weight (orderedPairInteger (shape 7 1 0) 5 1) : ℝ)
    have he : orderedPairInteger (shape 7 1 0) 5 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_1_0Raw (5,2)).Encloses (weight (orderedPairInteger (shape 7 1 0) 5 2) : ℝ)
    have he : orderedPairInteger (shape 7 1 0) 5 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_1_0Raw (5,3)).Encloses (weight (orderedPairInteger (shape 7 1 0) 5 3) : ℝ)
    have he : orderedPairInteger (shape 7 1 0) 5 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_1_0Raw (5,4)).Encloses (weight (orderedPairInteger (shape 7 1 0) 5 4) : ℝ)
    have he : orderedPairInteger (shape 7 1 0) 5 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_1_0Raw (5,5)).Encloses (weight (orderedPairInteger (shape 7 1 0) 5 5) : ℝ)
    have he : orderedPairInteger (shape 7 1 0) 5 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z7_1_0Raw_sound (ij : PairSlot) :
    (Z7_1_0Raw ij).Encloses (weight (orderedPairInteger (shape 7 1 0) ij.1 ij.2) : ℝ) := by
  rcases ij with ⟨i,j⟩
  revert i
  exact forall_fin6 (Z7_1_0Raw_sound_0 j) (Z7_1_0Raw_sound_1 j) (Z7_1_0Raw_sound_2 j) (Z7_1_0Raw_sound_3 j) (Z7_1_0Raw_sound_4 j) (Z7_1_0Raw_sound_5 j)
lemma Z7_1_0Den_sound : Z7_1_0Den.Encloses
    (((orderedPairs (shape 7 1 0)).map (fun ij => weight (orderedPairInteger (shape 7 1 0) ij.1 ij.2))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (orderedPairs (shape 7 1 0)) Z7_1_0Raw
    (fun ij => weight (orderedPairInteger (shape 7 1 0) ij.1 ij.2))
    (fun ij _ => Z7_1_0Raw_sound ij)) (by decide +kernel)
lemma Z7_1_0Den_pos : 0 < Z7_1_0Den.lower := by decide +kernel
lemma Z7_1_0Contains : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j = shapeMax (shape 7 1 0) →
    contains (.mul (Z7_1_0Raw (i,j)) (.inv Z7_1_0Den)) (Z7_1_0Probs (i,j)) = true := by
  decide +kernel
lemma Z7_1_0Zero : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j ≠ shapeMax (shape 7 1 0) → Z7_1_0Probs (i,j) = .exact 0 := by
  decide +kernel
lemma Z7_1_0Probs_sound (ij : PairSlot) :
    (Z7_1_0Probs ij).Encloses (zeroPairLaw (shape 7 1 0) ij.1 ij.2 : ℝ) := by
  by_cases h : statisticWeight ij.1 + statisticWeight ij.2 = shapeMax (shape 7 1 0)
  · have hb := contains_sound (Ball.mul_sound (Z7_1_0Raw_sound ij)
      (Ball.inv_sound Z7_1_0Den_sound Z7_1_0Den_pos)) (Z7_1_0Contains ij.1 ij.2 h)
    simpa only [zeroPairLaw, h, ite_true, if_true, Rat.cast_div, Rat.cast_mul,
      Rat.cast_inv, div_eq_mul_inv] using hb
  · rw [Z7_1_0Zero ij.1 ij.2 h]
    simpa only [zeroPairLaw, h, ite_false, if_false] using Ball.exact_sound 0

lemma Z7_1_0Half_sound (w : Fin 3) (ij : PairSlot) :
    (Z7_1_0Half w ij).Encloses (halfLaw (shape 7 1 0) w ij : ℝ) := by
  have hp : positive (shape 7 1 0) = false := by decide +kernel
  simp only [Z7_1_0Half, halfLaw, hp, Bool.false_eq_true, ite_false, if_false]
  split_ifs
  · exact Ball.exact_sound 1
  · exact Ball.exact_sound 0
  · exact Z7_1_0Probs_sound _
  · exact Z7_1_0Probs_sound _

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
lemma allSecond_list : shapes 8 = [
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
  (shape 2 6 0),
  (shape 3 0 5),
  (shape 3 1 4),
  (shape 3 2 3),
  (shape 3 3 2),
  (shape 3 4 1),
  (shape 3 5 0),
  (shape 4 0 4),
  (shape 4 1 3),
  (shape 4 2 2),
  (shape 4 3 1),
  (shape 4 4 0),
  (shape 5 0 3),
  (shape 5 1 2),
  (shape 5 2 1),
  (shape 5 3 0),
  (shape 6 0 2),
  (shape 6 1 1),
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
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SupportedContraction
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
lemma halfTable_sound_oai (t : Shape) (ht : t ∈ shapes 8) (w : Fin 3) (ij : PairSlot) :
    (halfTable t w ij).Encloses (halfLaw t w ij : ℝ) := by
  rw [allSecond_list] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Z0_0_8Half_sound w ij
  · exact Z0_1_7Half_sound w ij
  · exact Z0_2_6Half_sound w ij
  · exact Z0_3_5Half_sound w ij
  · exact Z0_4_4Half_sound w ij
  · exact Z0_5_3Half_sound w ij
  · exact Z0_6_2Half_sound w ij
  · exact Z0_7_1Half_sound w ij
  · exact Z0_8_0Half_sound w ij
  · exact Z1_0_7Half_sound w ij
  · exact B1_1_6Half_sound w ij
  · exact B1_2_5Half_sound w ij
  · exact B1_3_4Half_sound w ij
  · exact B1_4_3Half_sound w ij
  · exact B1_5_2Half_sound w ij
  · exact B1_6_1Half_sound w ij
  · exact Z1_7_0Half_sound w ij
  · exact Z2_0_6Half_sound w ij
  · exact B2_1_5Half_sound w ij
  · exact B2_2_4Half_sound w ij
  · exact B2_3_3Half_sound w ij
  · exact B2_4_2Half_sound w ij
  · exact B2_5_1Half_sound w ij
  · exact Z2_6_0Half_sound w ij
  · exact Z3_0_5Half_sound w ij
  · exact B3_1_4Half_sound w ij
  · exact B3_2_3Half_sound w ij
  · exact B3_3_2Half_sound w ij
  · exact B3_4_1Half_sound w ij
  · exact Z3_5_0Half_sound w ij
  · exact Z4_0_4Half_sound w ij
  · exact B4_1_3Half_sound w ij
  · exact B4_2_2Half_sound w ij
  · exact B4_3_1Half_sound w ij
  · exact Z4_4_0Half_sound w ij
  · exact Z5_0_3Half_sound w ij
  · exact B5_1_2Half_sound w ij
  · exact B5_2_1Half_sound w ij
  · exact Z5_3_0Half_sound w ij
  · exact Z6_0_2Half_sound w ij
  · exact B6_1_1Half_sound w ij
  · exact Z6_2_0Half_sound w ij
  · exact Z7_0_1Half_sound w ij
  · exact Z7_1_0Half_sound w ij
  · exact Z8_0_0Half_sound w ij

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.halfTable_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.halfTable_sound_oai
