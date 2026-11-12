-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2Raw_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T07:21:27.655281+00:00
-- url     : https://prove2.me/submissions/f8d7bae0-6a5b-4c98-bd1c-e0cbf12abcc5

import Mathlib
import Definitions.Def_OAIQ254M003
import Definitions.Def_OAIQ254M005
import Definitions.Def_OAIQ254M006
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_mul_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkPolynomial_sound

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
lemma w72_sound : w72.Encloses (weight (-26359) : ℝ) := by
  exact weight_enclosed_of_trace (-26359) w72Trace w72S0 w72S1 w72S2 w72S3 w72S4 w72S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w73_sound : w73.Encloses (weight (-26340) : ℝ) := by
  exact weight_enclosed_of_trace (-26340) w73Trace w73S0 w73S1 w73S2 w73S3 w73S4 w73S5
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
lemma w154_sound : w154.Encloses (weight (-6620) : ℝ) := by
  exact weight_enclosed_of_trace (-6620) w154Trace w154S0 w154S1 w154S2 w154S3 w154S4 w154S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

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
lemma B3_3_2Raw_0_2_2 : (B3_3_2Raw (shape 0 2 2)).Encloses (splitWeight positiveSecond tablep (shape 3 3 2) (shape 0 2 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 3 3 2) (shape 0 2 2)
    (-26340) (0) (-6620) w73 w195 w154
    (by decide +kernel) w73_sound w195_sound w154_sound) (by decide +kernel)
lemma B3_3_2Raw_0_3_1 : (B3_3_2Raw (shape 0 3 1)).Encloses (splitWeight positiveSecond tablep (shape 3 3 2) (shape 0 3 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 3 3 2) (shape 0 3 1)
    (-26340) (-26359) (0) w73 w72 w195
    (by decide +kernel) w73_sound w72_sound w195_sound) (by decide +kernel)
lemma B3_3_2Raw_1_1_2 : (B3_3_2Raw (shape 1 1 2)).Encloses (splitWeight positiveSecond tablep (shape 3 3 2) (shape 1 1 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 3 3 2) (shape 1 1 2)
    (0) (0) (-6620) w195 w195 w154
    (by decide +kernel) w195_sound w195_sound w154_sound) (by decide +kernel)
lemma B3_3_2Raw_1_2_1 : (B3_3_2Raw (shape 1 2 1)).Encloses (splitWeight positiveSecond tablep (shape 3 3 2) (shape 1 2 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 3 3 2) (shape 1 2 1)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma B3_3_2Raw_1_3_0 : (B3_3_2Raw (shape 1 3 0)).Encloses (splitWeight positiveSecond tablep (shape 3 3 2) (shape 1 3 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 3 3 2) (shape 1 3 0)
    (0) (-26359) (-6620) w195 w72 w154
    (by decide +kernel) w195_sound w72_sound w154_sound) (by decide +kernel)
lemma B3_3_2Raw_2_0_2 : (B3_3_2Raw (shape 2 0 2)).Encloses (splitWeight positiveSecond tablep (shape 3 3 2) (shape 2 0 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 3 3 2) (shape 2 0 2)
    (0) (-26359) (-6620) w195 w72 w154
    (by decide +kernel) w195_sound w72_sound w154_sound) (by decide +kernel)
lemma B3_3_2Raw_2_1_1 : (B3_3_2Raw (shape 2 1 1)).Encloses (splitWeight positiveSecond tablep (shape 3 3 2) (shape 2 1 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 3 3 2) (shape 2 1 1)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma B3_3_2Raw_2_2_0 : (B3_3_2Raw (shape 2 2 0)).Encloses (splitWeight positiveSecond tablep (shape 3 3 2) (shape 2 2 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 3 3 2) (shape 2 2 0)
    (0) (0) (-6620) w195 w195 w154
    (by decide +kernel) w195_sound w195_sound w154_sound) (by decide +kernel)
lemma B3_3_2Raw_3_0_1 : (B3_3_2Raw (shape 3 0 1)).Encloses (splitWeight positiveSecond tablep (shape 3 3 2) (shape 3 0 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 3 3 2) (shape 3 0 1)
    (-26340) (-26359) (0) w73 w72 w195
    (by decide +kernel) w73_sound w72_sound w195_sound) (by decide +kernel)
lemma B3_3_2Raw_3_1_0 : (B3_3_2Raw (shape 3 1 0)).Encloses (splitWeight positiveSecond tablep (shape 3 3 2) (shape 3 1 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 3 3 2) (shape 3 1 0)
    (-26340) (0) (-6620) w73 w195 w154
    (by decide +kernel) w73_sound w195_sound w154_sound) (by decide +kernel)
lemma B3_3_2Raw_sound_oai (u : Shape) (hu : u ∈ below (shape 3 3 2)) :
    (B3_3_2Raw u).Encloses (splitWeight positiveSecond tablep (shape 3 3 2) u : ℝ) := by
  rw [B3_3_2_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B3_3_2Raw_0_2_2
  · exact B3_3_2Raw_0_3_1
  · exact B3_3_2Raw_1_1_2
  · exact B3_3_2Raw_1_2_1
  · exact B3_3_2Raw_1_3_0
  · exact B3_3_2Raw_2_0_2
  · exact B3_3_2Raw_2_1_1
  · exact B3_3_2Raw_2_2_0
  · exact B3_3_2Raw_3_0_1
  · exact B3_3_2Raw_3_1_0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2Raw_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2Raw_sound_oai
