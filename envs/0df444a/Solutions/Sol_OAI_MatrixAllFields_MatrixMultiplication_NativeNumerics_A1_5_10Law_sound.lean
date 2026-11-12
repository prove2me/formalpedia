-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A1_5_10Law_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T07:14:05.583554+00:00
-- url     : https://prove2.me/submissions/733ead11-abe4-4cca-8538-d4dc88a40640

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
lemma w61_sound : w61.Encloses (weight (-32809) : ℝ) := by
  exact weight_enclosed_of_trace (-32809) w61Trace w61S0 w61S1 w61S2 w61S3 w61S4 w61S5
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
lemma w160_sound : w160.Encloses (weight (-5912) : ℝ) := by
  exact weight_enclosed_of_trace (-5912) w160Trace w160S0 w160S1 w160S2 w160S3 w160S4 w160S5
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
lemma w117_sound : w117.Encloses (weight (-14246) : ℝ) := by
  exact weight_enclosed_of_trace (-14246) w117Trace w117S0 w117S1 w117S2 w117S3 w117S4 w117S5
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
lemma w149_sound : w149.Encloses (weight (-7009) : ℝ) := by
  exact weight_enclosed_of_trace (-7009) w149Trace w149S0 w149S1 w149S2 w149S3 w149S4 w149S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitB1_3_4
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
lemma w8_sound : w8.Encloses (weight (-78106) : ℝ) := by
  exact weight_enclosed_of_trace (-78106) w8Trace w8S0 w8S1 w8S2 w8S3 w8S4 w8S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma A1_5_10_below : below (shape 1 5 10) = [
  (shape 0 0 8),
  (shape 0 1 7),
  (shape 0 2 6),
  (shape 0 3 5),
  (shape 0 4 4),
  (shape 0 5 3),
  (shape 1 0 7),
  (shape 1 1 6),
  (shape 1 2 5),
  (shape 1 3 4),
  (shape 1 4 3),
  (shape 1 5 2)] := by decide +kernel
lemma A1_5_10Raw_0_0_8 : (A1_5_10Raw (shape 0 0 8)).Encloses (splitWeight positiveInitial tableP (shape 1 5 10) (shape 0 0 8) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 5 10) (shape 0 0 8)
    (0) (-14246) (-78106) w195 w117 w8
    (by decide +kernel) w195_sound w117_sound w8_sound) (by decide +kernel)
lemma A1_5_10Raw_0_1_7 : (A1_5_10Raw (shape 0 1 7)).Encloses (splitWeight positiveInitial tableP (shape 1 5 10) (shape 0 1 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 5 10) (shape 0 1 7)
    (0) (-5912) (-32809) w195 w160 w61
    (by decide +kernel) w195_sound w160_sound w61_sound) (by decide +kernel)
lemma A1_5_10Raw_0_2_6 : (A1_5_10Raw (shape 0 2 6)).Encloses (splitWeight positiveInitial tableP (shape 1 5 10) (shape 0 2 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 5 10) (shape 0 2 6)
    (0) (0) (-7009) w195 w195 w149
    (by decide +kernel) w195_sound w195_sound w149_sound) (by decide +kernel)
lemma A1_5_10Raw_0_3_5 : (A1_5_10Raw (shape 0 3 5)).Encloses (splitWeight positiveInitial tableP (shape 1 5 10) (shape 0 3 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 5 10) (shape 0 3 5)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A1_5_10Raw_0_4_4 : (A1_5_10Raw (shape 0 4 4)).Encloses (splitWeight positiveInitial tableP (shape 1 5 10) (shape 0 4 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 5 10) (shape 0 4 4)
    (0) (-5912) (-7009) w195 w160 w149
    (by decide +kernel) w195_sound w160_sound w149_sound) (by decide +kernel)
lemma A1_5_10Raw_0_5_3 : (A1_5_10Raw (shape 0 5 3)).Encloses (splitWeight positiveInitial tableP (shape 1 5 10) (shape 0 5 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 5 10) (shape 0 5 3)
    (0) (-14246) (-32809) w195 w117 w61
    (by decide +kernel) w195_sound w117_sound w61_sound) (by decide +kernel)
lemma A1_5_10Raw_1_0_7 : (A1_5_10Raw (shape 1 0 7)).Encloses (splitWeight positiveInitial tableP (shape 1 5 10) (shape 1 0 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 5 10) (shape 1 0 7)
    (0) (-14246) (-32809) w195 w117 w61
    (by decide +kernel) w195_sound w117_sound w61_sound) (by decide +kernel)
lemma A1_5_10Raw_1_1_6 : (A1_5_10Raw (shape 1 1 6)).Encloses (splitWeight positiveInitial tableP (shape 1 5 10) (shape 1 1 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 5 10) (shape 1 1 6)
    (0) (-5912) (-7009) w195 w160 w149
    (by decide +kernel) w195_sound w160_sound w149_sound) (by decide +kernel)
lemma A1_5_10Raw_1_2_5 : (A1_5_10Raw (shape 1 2 5)).Encloses (splitWeight positiveInitial tableP (shape 1 5 10) (shape 1 2 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 5 10) (shape 1 2 5)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A1_5_10Raw_1_3_4 : (A1_5_10Raw (shape 1 3 4)).Encloses (splitWeight positiveInitial tableP (shape 1 5 10) (shape 1 3 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 5 10) (shape 1 3 4)
    (0) (0) (-7009) w195 w195 w149
    (by decide +kernel) w195_sound w195_sound w149_sound) (by decide +kernel)
lemma A1_5_10Raw_1_4_3 : (A1_5_10Raw (shape 1 4 3)).Encloses (splitWeight positiveInitial tableP (shape 1 5 10) (shape 1 4 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 5 10) (shape 1 4 3)
    (0) (-5912) (-32809) w195 w160 w61
    (by decide +kernel) w195_sound w160_sound w61_sound) (by decide +kernel)
lemma A1_5_10Raw_1_5_2 : (A1_5_10Raw (shape 1 5 2)).Encloses (splitWeight positiveInitial tableP (shape 1 5 10) (shape 1 5 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 5 10) (shape 1 5 2)
    (0) (-14246) (-78106) w195 w117 w8
    (by decide +kernel) w195_sound w117_sound w8_sound) (by decide +kernel)
lemma A1_5_10Raw_sound (u : Shape) (hu : u ∈ below (shape 1 5 10)) :
    (A1_5_10Raw u).Encloses (splitWeight positiveInitial tableP (shape 1 5 10) u : ℝ) := by
  rw [A1_5_10_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A1_5_10Raw_0_0_8
  · exact A1_5_10Raw_0_1_7
  · exact A1_5_10Raw_0_2_6
  · exact A1_5_10Raw_0_3_5
  · exact A1_5_10Raw_0_4_4
  · exact A1_5_10Raw_0_5_3
  · exact A1_5_10Raw_1_0_7
  · exact A1_5_10Raw_1_1_6
  · exact A1_5_10Raw_1_2_5
  · exact A1_5_10Raw_1_3_4
  · exact A1_5_10Raw_1_4_3
  · exact A1_5_10Raw_1_5_2
lemma A1_5_10Den_sound : A1_5_10Den.Encloses (((below (shape 1 5 10)).map (splitWeight positiveInitial tableP (shape 1 5 10))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (below (shape 1 5 10)) A1_5_10Raw (splitWeight positiveInitial tableP (shape 1 5 10)) A1_5_10Raw_sound) (by decide +kernel)
lemma A1_5_10Den_positive : 0 < A1_5_10Den.lower := by decide +kernel
lemma A1_5_10Law_check_0_0_8 : contains (.mul (A1_5_10Raw (shape 0 0 8)) (.inv A1_5_10Den)) (A1_5_10Table (shape 0 0 8)) = true := by decide +kernel
lemma A1_5_10Law_check_0_1_7 : contains (.mul (A1_5_10Raw (shape 0 1 7)) (.inv A1_5_10Den)) (A1_5_10Table (shape 0 1 7)) = true := by decide +kernel
lemma A1_5_10Law_check_0_2_6 : contains (.mul (A1_5_10Raw (shape 0 2 6)) (.inv A1_5_10Den)) (A1_5_10Table (shape 0 2 6)) = true := by decide +kernel
lemma A1_5_10Law_check_0_3_5 : contains (.mul (A1_5_10Raw (shape 0 3 5)) (.inv A1_5_10Den)) (A1_5_10Table (shape 0 3 5)) = true := by decide +kernel
lemma A1_5_10Law_check_0_4_4 : contains (.mul (A1_5_10Raw (shape 0 4 4)) (.inv A1_5_10Den)) (A1_5_10Table (shape 0 4 4)) = true := by decide +kernel
lemma A1_5_10Law_check_0_5_3 : contains (.mul (A1_5_10Raw (shape 0 5 3)) (.inv A1_5_10Den)) (A1_5_10Table (shape 0 5 3)) = true := by decide +kernel
lemma A1_5_10Law_check_1_0_7 : contains (.mul (A1_5_10Raw (shape 1 0 7)) (.inv A1_5_10Den)) (A1_5_10Table (shape 1 0 7)) = true := by decide +kernel
lemma A1_5_10Law_check_1_1_6 : contains (.mul (A1_5_10Raw (shape 1 1 6)) (.inv A1_5_10Den)) (A1_5_10Table (shape 1 1 6)) = true := by decide +kernel
lemma A1_5_10Law_check_1_2_5 : contains (.mul (A1_5_10Raw (shape 1 2 5)) (.inv A1_5_10Den)) (A1_5_10Table (shape 1 2 5)) = true := by decide +kernel
lemma A1_5_10Law_check_1_3_4 : contains (.mul (A1_5_10Raw (shape 1 3 4)) (.inv A1_5_10Den)) (A1_5_10Table (shape 1 3 4)) = true := by decide +kernel
lemma A1_5_10Law_check_1_4_3 : contains (.mul (A1_5_10Raw (shape 1 4 3)) (.inv A1_5_10Den)) (A1_5_10Table (shape 1 4 3)) = true := by decide +kernel
lemma A1_5_10Law_check_1_5_2 : contains (.mul (A1_5_10Raw (shape 1 5 2)) (.inv A1_5_10Den)) (A1_5_10Table (shape 1 5 2)) = true := by decide +kernel
lemma A1_5_10Law_check (u : Shape) (hu : u ∈ below (shape 1 5 10)) :
    contains (.mul (A1_5_10Raw u) (.inv A1_5_10Den)) (A1_5_10Table u) = true := by
  rw [A1_5_10_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A1_5_10Law_check_0_0_8
  · exact A1_5_10Law_check_0_1_7
  · exact A1_5_10Law_check_0_2_6
  · exact A1_5_10Law_check_0_3_5
  · exact A1_5_10Law_check_0_4_4
  · exact A1_5_10Law_check_0_5_3
  · exact A1_5_10Law_check_1_0_7
  · exact A1_5_10Law_check_1_1_6
  · exact A1_5_10Law_check_1_2_5
  · exact A1_5_10Law_check_1_3_4
  · exact A1_5_10Law_check_1_4_3
  · exact A1_5_10Law_check_1_5_2
lemma A1_5_10Law_sound_oai (u : Shape) :
    (A1_5_10Law u).Encloses (stageALaw (shape 1 5 10) u : ℝ) := by
  by_cases hu : u ∈ below (shape 1 5 10)
  · have h := contains_sound (Ball.mul_sound (A1_5_10Raw_sound u hu)
      (Ball.inv_sound A1_5_10Den_sound A1_5_10Den_positive)) (A1_5_10Law_check u hu)
    simpa only [A1_5_10Law, hu, ite_true, if_true, stageALaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [A1_5_10Law, hu, ite_false, if_false, stageALaw, splitLaw, Rat.cast_zero]
    simpa only [Rat.cast_zero] using Ball.exact_sound 0

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A1_5_10Law_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A1_5_10Law_sound_oai
