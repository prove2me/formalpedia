-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A1_3_12Law_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:48:48.381403+00:00
-- url     : https://prove2.me/submissions/98075c9e-6bf5-48af-b9a5-84c02998f58e

import Mathlib
import Definitions.Def_OAIQ254M003
import Definitions.Def_OAIQ254M005
import Definitions.Def_OAIQ254M006
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_mul_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkPolynomial_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_A1_3_12Den_sound

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

theorem ofBounds_sound {lo hi : ℚ} {x : ℝ}
    (hlo : (lo : ℝ) ≤ x) (hhi : x ≤ (hi : ℝ)) :
    (ofBounds lo hi).Encloses x := by
  simp only [Encloses, ofBounds, Rat.cast_add, Rat.cast_div, Rat.cast_ofNat,
    Rat.cast_sub]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem inv_sound {a : Ball} {x : ℝ} (hx : a.Encloses x)
    (hpos : 0 < a.lower) : (inv a).Encloses x⁻¹ := by
  have hlo : (0 : ℝ) < a.lower := by exact_mod_cast hpos
  obtain ⟨hl, hu⟩ := bounds hx
  have hxp : 0 < x := lt_of_lt_of_le hlo hl
  apply ofBounds_sound
  · simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_inv, one_div] using
      one_div_le_one_div_of_le hxp hu
  · simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_inv, one_div] using
      one_div_le_one_div_of_le hlo hl

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
lemma w191_sound : w191.Encloses (weight (-1514) : ℝ) := by
  exact weight_enclosed_of_trace (-1514) w191Trace w191S0 w191S1 w191S2 w191S3 w191S4 w191S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

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
lemma w47_sound : w47.Encloses (weight (-38211) : ℝ) := by
  exact weight_enclosed_of_trace (-38211) w47Trace w47S0 w47S1 w47S2 w47S3 w47S4 w47S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

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
lemma w134_sound : w134.Encloses (weight (-9654) : ℝ) := by
  exact weight_enclosed_of_trace (-9654) w134Trace w134S0 w134S1 w134S2 w134S3 w134S4 w134S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
lemma A1_3_12_below : below (shape 1 3 12) = [
  (shape 0 0 8),
  (shape 0 1 7),
  (shape 0 2 6),
  (shape 0 3 5),
  (shape 1 0 7),
  (shape 1 1 6),
  (shape 1 2 5),
  (shape 1 3 4)] := by decide +kernel
lemma A1_3_12Raw_0_0_8 : (A1_3_12Raw (shape 0 0 8)).Encloses (splitWeight positiveInitial tableP (shape 1 3 12) (shape 0 0 8) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 3 12) (shape 0 0 8)
    (0) (-1514) (-38211) w195 w191 w47
    (by decide +kernel) w195_sound w191_sound w47_sound) (by decide +kernel)
lemma A1_3_12Raw_0_1_7 : (A1_3_12Raw (shape 0 1 7)).Encloses (splitWeight positiveInitial tableP (shape 1 3 12) (shape 0 1 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 3 12) (shape 0 1 7)
    (0) (0) (-9654) w195 w195 w134
    (by decide +kernel) w195_sound w195_sound w134_sound) (by decide +kernel)
lemma A1_3_12Raw_0_2_6 : (A1_3_12Raw (shape 0 2 6)).Encloses (splitWeight positiveInitial tableP (shape 1 3 12) (shape 0 2 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 3 12) (shape 0 2 6)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A1_3_12Raw_0_3_5 : (A1_3_12Raw (shape 0 3 5)).Encloses (splitWeight positiveInitial tableP (shape 1 3 12) (shape 0 3 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 3 12) (shape 0 3 5)
    (0) (-1514) (-9654) w195 w191 w134
    (by decide +kernel) w195_sound w191_sound w134_sound) (by decide +kernel)
lemma A1_3_12Raw_1_0_7 : (A1_3_12Raw (shape 1 0 7)).Encloses (splitWeight positiveInitial tableP (shape 1 3 12) (shape 1 0 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 3 12) (shape 1 0 7)
    (0) (-1514) (-9654) w195 w191 w134
    (by decide +kernel) w195_sound w191_sound w134_sound) (by decide +kernel)
lemma A1_3_12Raw_1_1_6 : (A1_3_12Raw (shape 1 1 6)).Encloses (splitWeight positiveInitial tableP (shape 1 3 12) (shape 1 1 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 3 12) (shape 1 1 6)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A1_3_12Raw_1_2_5 : (A1_3_12Raw (shape 1 2 5)).Encloses (splitWeight positiveInitial tableP (shape 1 3 12) (shape 1 2 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 3 12) (shape 1 2 5)
    (0) (0) (-9654) w195 w195 w134
    (by decide +kernel) w195_sound w195_sound w134_sound) (by decide +kernel)
lemma A1_3_12Raw_1_3_4 : (A1_3_12Raw (shape 1 3 4)).Encloses (splitWeight positiveInitial tableP (shape 1 3 12) (shape 1 3 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 3 12) (shape 1 3 4)
    (0) (-1514) (-38211) w195 w191 w47
    (by decide +kernel) w195_sound w191_sound w47_sound) (by decide +kernel)
lemma A1_3_12Raw_sound (u : Shape) (hu : u ∈ below (shape 1 3 12)) :
    (A1_3_12Raw u).Encloses (splitWeight positiveInitial tableP (shape 1 3 12) u : ℝ) := by
  rw [A1_3_12_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A1_3_12Raw_0_0_8
  · exact A1_3_12Raw_0_1_7
  · exact A1_3_12Raw_0_2_6
  · exact A1_3_12Raw_0_3_5
  · exact A1_3_12Raw_1_0_7
  · exact A1_3_12Raw_1_1_6
  · exact A1_3_12Raw_1_2_5
  · exact A1_3_12Raw_1_3_4
lemma A1_3_12Den_positive : 0 < A1_3_12Den.lower := by decide +kernel
lemma A1_3_12Law_check_0_0_8 : contains (.mul (A1_3_12Raw (shape 0 0 8)) (.inv A1_3_12Den)) (A1_3_12Table (shape 0 0 8)) = true := by decide +kernel
lemma A1_3_12Law_check_0_1_7 : contains (.mul (A1_3_12Raw (shape 0 1 7)) (.inv A1_3_12Den)) (A1_3_12Table (shape 0 1 7)) = true := by decide +kernel
lemma A1_3_12Law_check_0_2_6 : contains (.mul (A1_3_12Raw (shape 0 2 6)) (.inv A1_3_12Den)) (A1_3_12Table (shape 0 2 6)) = true := by decide +kernel
lemma A1_3_12Law_check_0_3_5 : contains (.mul (A1_3_12Raw (shape 0 3 5)) (.inv A1_3_12Den)) (A1_3_12Table (shape 0 3 5)) = true := by decide +kernel
lemma A1_3_12Law_check_1_0_7 : contains (.mul (A1_3_12Raw (shape 1 0 7)) (.inv A1_3_12Den)) (A1_3_12Table (shape 1 0 7)) = true := by decide +kernel
lemma A1_3_12Law_check_1_1_6 : contains (.mul (A1_3_12Raw (shape 1 1 6)) (.inv A1_3_12Den)) (A1_3_12Table (shape 1 1 6)) = true := by decide +kernel
lemma A1_3_12Law_check_1_2_5 : contains (.mul (A1_3_12Raw (shape 1 2 5)) (.inv A1_3_12Den)) (A1_3_12Table (shape 1 2 5)) = true := by decide +kernel
lemma A1_3_12Law_check_1_3_4 : contains (.mul (A1_3_12Raw (shape 1 3 4)) (.inv A1_3_12Den)) (A1_3_12Table (shape 1 3 4)) = true := by decide +kernel
lemma A1_3_12Law_check (u : Shape) (hu : u ∈ below (shape 1 3 12)) :
    contains (.mul (A1_3_12Raw u) (.inv A1_3_12Den)) (A1_3_12Table u) = true := by
  rw [A1_3_12_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A1_3_12Law_check_0_0_8
  · exact A1_3_12Law_check_0_1_7
  · exact A1_3_12Law_check_0_2_6
  · exact A1_3_12Law_check_0_3_5
  · exact A1_3_12Law_check_1_0_7
  · exact A1_3_12Law_check_1_1_6
  · exact A1_3_12Law_check_1_2_5
  · exact A1_3_12Law_check_1_3_4
lemma A1_3_12Law_sound_oai (u : Shape) :
    (A1_3_12Law u).Encloses (stageALaw (shape 1 3 12) u : ℝ) := by
  by_cases hu : u ∈ below (shape 1 3 12)
  · have h := contains_sound (Ball.mul_sound (A1_3_12Raw_sound u hu)
      (Ball.inv_sound A1_3_12Den_sound A1_3_12Den_positive)) (A1_3_12Law_check u hu)
    simpa only [A1_3_12Law, hu, ite_true, if_true, stageALaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [A1_3_12Law, hu, ite_false, if_false, stageALaw, splitLaw, Rat.cast_zero]
    simpa only [Rat.cast_zero] using Ball.exact_sound 0

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A1_3_12Law_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A1_3_12Law_sound_oai
