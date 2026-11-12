-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_6_1Den_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:48:50.190192+00:00
-- url     : https://prove2.me/submissions/f22f5d18-ffff-4b29-9091-844280bb650e

import Mathlib
import Definitions.Def_OAIQ254M003
import Definitions.Def_OAIQ254M005
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_mul_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkPolynomial_sound
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
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.shapeValue_relot
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

lemma splitWeight_three_enclosed (parents : List Shape) (data : List ℤ)
    (s u : Shape) (n₀ n₁ n₂ : ℤ) (b₀ b₁ b₂ : Ball)
    (hsig : splitSignature parents data s u = (Matrix.vecCons (n₀) (Matrix.vecCons (n₁) (Matrix.vecCons (n₂) Matrix.vecEmpty))))
    (h₀ : b₀.Encloses (weight n₀ : ℝ))
    (h₁ : b₁.Encloses (weight n₁ : ℝ))
    (h₂ : b₂.Encloses (weight n₂ : ℝ)) :
    (Ball.mul b₀ (Ball.mul b₁ b₂)).Encloses (splitWeight parents data s u : ℝ) := by
  convert Ball.mul_sound h₀ (Ball.mul_sound h₁ h₂) using 1
  all_goals try with_reducible_and_instances rfl
  simp [splitWeight, hsig, Fin.prod_univ_succ]

lemma list_cast_enclosed {A : Type*} (xs : List A) (b : A → Ball) (v : A → ℚ)
    (h : ∀ a ∈ xs, (b a).Encloses (v a : ℝ)) :
    (listSumBall xs b).Encloses ((xs.map v).sum : ℝ) := by
  simpa only [Rat.cast_list_sum, List.map_map, Function.comp_def] using
    listSumBall_sound xs b (fun a => (v a : ℝ)) h

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
lemma w124_sound : w124.Encloses (weight (-11688) : ℝ) := by
  exact weight_enclosed_of_trace (-11688) w124Trace w124S0 w124S1 w124S2 w124S3 w124S4 w124S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal1_6_1
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
lemma B1_6_1_below : below (shape 1 6 1) = [
  (shape 0 3 1),
  (shape 0 4 0),
  (shape 1 2 1),
  (shape 1 3 0)] := by decide +kernel
lemma B1_6_1Raw_0_3_1 : (B1_6_1Raw (shape 0 3 1)).Encloses (splitWeight positiveSecond tablep (shape 1 6 1) (shape 0 3 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 1 6 1) (shape 0 3 1)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma B1_6_1Raw_0_4_0 : (B1_6_1Raw (shape 0 4 0)).Encloses (splitWeight positiveSecond tablep (shape 1 6 1) (shape 0 4 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 1 6 1) (shape 0 4 0)
    (0) (-11688) (0) w195 w124 w195
    (by decide +kernel) w195_sound w124_sound w195_sound) (by decide +kernel)
lemma B1_6_1Raw_1_2_1 : (B1_6_1Raw (shape 1 2 1)).Encloses (splitWeight positiveSecond tablep (shape 1 6 1) (shape 1 2 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 1 6 1) (shape 1 2 1)
    (0) (-11688) (0) w195 w124 w195
    (by decide +kernel) w195_sound w124_sound w195_sound) (by decide +kernel)
lemma B1_6_1Raw_1_3_0 : (B1_6_1Raw (shape 1 3 0)).Encloses (splitWeight positiveSecond tablep (shape 1 6 1) (shape 1 3 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 1 6 1) (shape 1 3 0)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma B1_6_1Raw_sound (u : Shape) (hu : u ∈ below (shape 1 6 1)) :
    (B1_6_1Raw u).Encloses (splitWeight positiveSecond tablep (shape 1 6 1) u : ℝ) := by
  rw [B1_6_1_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl
  · exact B1_6_1Raw_0_3_1
  · exact B1_6_1Raw_0_4_0
  · exact B1_6_1Raw_1_2_1
  · exact B1_6_1Raw_1_3_0
lemma B1_6_1Den_sound_oai : B1_6_1Den.Encloses (((below (shape 1 6 1)).map (splitWeight positiveSecond tablep (shape 1 6 1))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (below (shape 1 6 1)) B1_6_1Raw (splitWeight positiveSecond tablep (shape 1 6 1)) B1_6_1Raw_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_6_1Den_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_6_1Den_sound_oai
