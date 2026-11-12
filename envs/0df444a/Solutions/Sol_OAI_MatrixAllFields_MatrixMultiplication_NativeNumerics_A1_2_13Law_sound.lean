-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A1_2_13Law_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:48:46.497276+00:00
-- url     : https://prove2.me/submissions/cdf0e399-fb77-4163-a295-fbc788478ea9

import Mathlib
import Definitions.Def_OAIQ254M003
import Definitions.Def_OAIQ254M005
import Definitions.Def_OAIQ254M006
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

theorem add_sound {a b : Ball} {x y : ℝ} (hx : a.Encloses x) (hy : b.Encloses y) :
    (add a b).Encloses (x + y) := by
  unfold Encloses add
  simp only [Rat.cast_add]
  calc
    _ = |(x - (a.center : ℝ)) + (y - (b.center : ℝ))| := by congr 1; ring
    _ ≤ |x - (a.center : ℝ)| + |y - (b.center : ℝ)| := abs_add_le _ _
    _ ≤ _ := add_le_add hx hy

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

lemma w198_sound : w198.Encloses (weight (295) : ℝ) := by
  exact weight_enclosed_of_trace (295) w198Trace w198S0 w198S1 w198S2 w198S3 w198S4 w198S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitB2_3_3
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
lemma w84_sound : w84.Encloses (weight (-20546) : ℝ) := by
  exact weight_enclosed_of_trace (-20546) w84Trace w84S0 w84S1 w84S2 w84S3 w84S4 w84S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma A1_2_13_below : below (shape 1 2 13) = [
  (shape 0 0 8),
  (shape 0 1 7),
  (shape 0 2 6),
  (shape 1 0 7),
  (shape 1 1 6),
  (shape 1 2 5)] := by decide +kernel
lemma A1_2_13Raw_0_0_8 : (A1_2_13Raw (shape 0 0 8)).Encloses (splitWeight positiveInitial tableP (shape 1 2 13) (shape 0 0 8) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 2 13) (shape 0 0 8)
    (0) (295) (-20546) w195 w198 w84
    (by decide +kernel) w195_sound w198_sound w84_sound) (by decide +kernel)
lemma A1_2_13Raw_0_1_7 : (A1_2_13Raw (shape 0 1 7)).Encloses (splitWeight positiveInitial tableP (shape 1 2 13) (shape 0 1 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 2 13) (shape 0 1 7)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A1_2_13Raw_0_2_6 : (A1_2_13Raw (shape 0 2 6)).Encloses (splitWeight positiveInitial tableP (shape 1 2 13) (shape 0 2 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 2 13) (shape 0 2 6)
    (0) (295) (0) w195 w198 w195
    (by decide +kernel) w195_sound w198_sound w195_sound) (by decide +kernel)
lemma A1_2_13Raw_1_0_7 : (A1_2_13Raw (shape 1 0 7)).Encloses (splitWeight positiveInitial tableP (shape 1 2 13) (shape 1 0 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 2 13) (shape 1 0 7)
    (0) (295) (0) w195 w198 w195
    (by decide +kernel) w195_sound w198_sound w195_sound) (by decide +kernel)
lemma A1_2_13Raw_1_1_6 : (A1_2_13Raw (shape 1 1 6)).Encloses (splitWeight positiveInitial tableP (shape 1 2 13) (shape 1 1 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 2 13) (shape 1 1 6)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A1_2_13Raw_1_2_5 : (A1_2_13Raw (shape 1 2 5)).Encloses (splitWeight positiveInitial tableP (shape 1 2 13) (shape 1 2 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 2 13) (shape 1 2 5)
    (0) (295) (-20546) w195 w198 w84
    (by decide +kernel) w195_sound w198_sound w84_sound) (by decide +kernel)
lemma A1_2_13Raw_sound (u : Shape) (hu : u ∈ below (shape 1 2 13)) :
    (A1_2_13Raw u).Encloses (splitWeight positiveInitial tableP (shape 1 2 13) u : ℝ) := by
  rw [A1_2_13_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · exact A1_2_13Raw_0_0_8
  · exact A1_2_13Raw_0_1_7
  · exact A1_2_13Raw_0_2_6
  · exact A1_2_13Raw_1_0_7
  · exact A1_2_13Raw_1_1_6
  · exact A1_2_13Raw_1_2_5
lemma A1_2_13Den_sound : A1_2_13Den.Encloses (((below (shape 1 2 13)).map (splitWeight positiveInitial tableP (shape 1 2 13))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (below (shape 1 2 13)) A1_2_13Raw (splitWeight positiveInitial tableP (shape 1 2 13)) A1_2_13Raw_sound) (by decide +kernel)
lemma A1_2_13Den_positive : 0 < A1_2_13Den.lower := by decide +kernel
lemma A1_2_13Law_check_0_0_8 : contains (.mul (A1_2_13Raw (shape 0 0 8)) (.inv A1_2_13Den)) (A1_2_13Table (shape 0 0 8)) = true := by decide +kernel
lemma A1_2_13Law_check_0_1_7 : contains (.mul (A1_2_13Raw (shape 0 1 7)) (.inv A1_2_13Den)) (A1_2_13Table (shape 0 1 7)) = true := by decide +kernel
lemma A1_2_13Law_check_0_2_6 : contains (.mul (A1_2_13Raw (shape 0 2 6)) (.inv A1_2_13Den)) (A1_2_13Table (shape 0 2 6)) = true := by decide +kernel
lemma A1_2_13Law_check_1_0_7 : contains (.mul (A1_2_13Raw (shape 1 0 7)) (.inv A1_2_13Den)) (A1_2_13Table (shape 1 0 7)) = true := by decide +kernel
lemma A1_2_13Law_check_1_1_6 : contains (.mul (A1_2_13Raw (shape 1 1 6)) (.inv A1_2_13Den)) (A1_2_13Table (shape 1 1 6)) = true := by decide +kernel
lemma A1_2_13Law_check_1_2_5 : contains (.mul (A1_2_13Raw (shape 1 2 5)) (.inv A1_2_13Den)) (A1_2_13Table (shape 1 2 5)) = true := by decide +kernel
lemma A1_2_13Law_check (u : Shape) (hu : u ∈ below (shape 1 2 13)) :
    contains (.mul (A1_2_13Raw u) (.inv A1_2_13Den)) (A1_2_13Table u) = true := by
  rw [A1_2_13_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · exact A1_2_13Law_check_0_0_8
  · exact A1_2_13Law_check_0_1_7
  · exact A1_2_13Law_check_0_2_6
  · exact A1_2_13Law_check_1_0_7
  · exact A1_2_13Law_check_1_1_6
  · exact A1_2_13Law_check_1_2_5
lemma A1_2_13Law_sound_oai (u : Shape) :
    (A1_2_13Law u).Encloses (stageALaw (shape 1 2 13) u : ℝ) := by
  by_cases hu : u ∈ below (shape 1 2 13)
  · have h := contains_sound (Ball.mul_sound (A1_2_13Raw_sound u hu)
      (Ball.inv_sound A1_2_13Den_sound A1_2_13Den_positive)) (A1_2_13Law_check u hu)
    simpa only [A1_2_13Law, hu, ite_true, if_true, stageALaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [A1_2_13Law, hu, ite_false, if_false, stageALaw, splitLaw, Rat.cast_zero]
    simpa only [Rat.cast_zero] using Ball.exact_sound 0

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A1_2_13Law_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A1_2_13Law_sound_oai
