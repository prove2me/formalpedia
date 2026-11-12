-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B5_1_2S2_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T06:43:58.439481+00:00
-- url     : https://prove2.me/submissions/3fec3ea7-4f70-4cf6-94fd-2f8e3915447a

import Mathlib
import Definitions.Def_OAIQ254M002
import Definitions.Def_OAIQ254M003
import Definitions.Def_OAIQ254M005
import Definitions.Def_OAIQ254M006
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkLog_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkPolynomial_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_normalizedLogBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_AProbsTable_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_initialProbs_sound

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_CertificatesReplay
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons
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

theorem nonnegative_radius {b : Ball} {x : ℝ} (h : b.Encloses x) : 0 ≤ b.radius := by
  have : (0 : ℝ) ≤ b.radius := (abs_nonneg _).trans h
  exact_mod_cast this

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

theorem exact_sound (q : ℚ) : (exact q).Encloses (q : ℝ) := by
  simp [Encloses, exact]

theorem add_sound {a b : Ball} {x y : ℝ} (hx : a.Encloses x) (hy : b.Encloses y) :
    (add a b).Encloses (x + y) := by
  unfold Encloses add
  simp only [Rat.cast_add]
  calc
    _ = |(x - (a.center : ℝ)) + (y - (b.center : ℝ))| := by congr 1; ring
    _ ≤ |x - (a.center : ℝ)| + |y - (b.center : ℝ)| := abs_add_le _ _
    _ ≤ _ := add_le_add hx hy

theorem neg_sound {a : Ball} {x : ℝ} (hx : a.Encloses x) :
    (neg a).Encloses (-x) := by
  simpa only [Encloses, neg, Rat.cast_neg, neg_sub_neg, abs_sub_comm] using hx

theorem mul_sound {a b : Ball} {x y : ℝ} (hx : a.Encloses x) (hy : b.Encloses y) :
    (mul a b).Encloses (x * y) := by
  have ha : (0 : ℝ) ≤ a.radius := by exact_mod_cast nonnegative_radius hx
  have hb : (0 : ℝ) ≤ b.radius := by exact_mod_cast nonnegative_radius hy
  unfold Encloses mul
  simp only [Rat.cast_mul, Rat.cast_add, Rat.cast_abs]
  calc
    _ = |(a.center : ℝ) * (y - (b.center : ℝ)) +
          (b.center : ℝ) * (x - (a.center : ℝ)) +
          (x - (a.center : ℝ)) * (y - (b.center : ℝ))| := by congr 1; ring
    _ ≤ |(a.center : ℝ) * (y - (b.center : ℝ))| +
          |(b.center : ℝ) * (x - (a.center : ℝ))| +
          |(x - (a.center : ℝ)) * (y - (b.center : ℝ))| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))
    _ = |(a.center : ℝ)| * |y - (b.center : ℝ)| +
          |(b.center : ℝ)| * |x - (a.center : ℝ)| +
          |x - (a.center : ℝ)| * |y - (b.center : ℝ)| := by simp only [abs_mul]
    _ ≤ _ := add_le_add
      (add_le_add (mul_le_mul_of_nonneg_left hy (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hx (abs_nonneg _)))
      (mul_le_mul hx hy (abs_nonneg _) ha)

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
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.shapeValue_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inl
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

lemma logTwoBall_sound : logTwoBall.Encloses (Real.log 2) := by
  have h := normalizedLogBall_sound (m := 2) (trace := logTwoTrace)
    (by norm_num) (by norm_num) (by decide +kernel)
  exact contains_sound h (by decide +kernel)

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

lemma entropyTerm_ball {p : ℝ} {b l : Ball} (hb : b.Encloses p)
    (hl : l.Encloses (Real.log p)) :
    (Ball.mul (Ball.neg b) l).Encloses (Foundation.entropyTerm p) :=
  Ball.mul_sound (Ball.neg_sound hb) hl

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

lemma exact_rat_enclosed {q r : ℚ} (h : q = r) : (Ball.exact q).Encloses (r : ℝ) := by
  rw [h]
  exact Ball.exact_sound r

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
lemma logN2_sound : logN2.Encloses (Real.log ((2 : ℝ))) := by
  exact checkLog_sound logTwoBall_sound ((by convert Ball.exact_sound (2 : ℚ) using 1; norm_num)) (w := logN2Witness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma logN5_sound : logN5.Encloses (Real.log ((5 : ℝ))) := by
  exact checkLog_sound logTwoBall_sound ((by convert Ball.exact_sound (5 : ℚ) using 1; norm_num)) (w := logN5Witness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma logN10_sound : logN10.Encloses (Real.log ((10 : ℝ))) := by
  exact checkLog_sound logTwoBall_sound ((by convert Ball.exact_sound (10 : ℚ) using 1; norm_num)) (w := logN10Witness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)

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
lemma w66_sound : w66.Encloses (weight (-32128) : ℝ) := by
  exact weight_enclosed_of_trace (-32128) w66Trace w66S0 w66S1 w66S2 w66S3 w66S4 w66S5
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
lemma w161_sound : w161.Encloses (weight (-5727) : ℝ) := by
  exact weight_enclosed_of_trace (-5727) w161Trace w161S0 w161S1 w161S2 w161S3 w161S4 w161S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma B5_1_2_below : below (shape 5 1 2) = [
  (shape 1 1 2),
  (shape 2 0 2),
  (shape 2 1 1),
  (shape 3 0 1),
  (shape 3 1 0),
  (shape 4 0 0)] := by decide +kernel
lemma B5_1_2Raw_1_1_2 : (B5_1_2Raw (shape 1 1 2)).Encloses (splitWeight positiveSecond tablep (shape 5 1 2) (shape 1 1 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 5 1 2) (shape 1 1 2)
    (-32128) (0) (-5727) w66 w195 w161
    (by decide +kernel) w66_sound w195_sound w161_sound) (by decide +kernel)
lemma B5_1_2Raw_2_0_2 : (B5_1_2Raw (shape 2 0 2)).Encloses (splitWeight positiveSecond tablep (shape 5 1 2) (shape 2 0 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 5 1 2) (shape 2 0 2)
    (0) (0) (-5727) w195 w195 w161
    (by decide +kernel) w195_sound w195_sound w161_sound) (by decide +kernel)
lemma B5_1_2Raw_2_1_1 : (B5_1_2Raw (shape 2 1 1)).Encloses (splitWeight positiveSecond tablep (shape 5 1 2) (shape 2 1 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 5 1 2) (shape 2 1 1)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma B5_1_2Raw_3_0_1 : (B5_1_2Raw (shape 3 0 1)).Encloses (splitWeight positiveSecond tablep (shape 5 1 2) (shape 3 0 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 5 1 2) (shape 3 0 1)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma B5_1_2Raw_3_1_0 : (B5_1_2Raw (shape 3 1 0)).Encloses (splitWeight positiveSecond tablep (shape 5 1 2) (shape 3 1 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 5 1 2) (shape 3 1 0)
    (0) (0) (-5727) w195 w195 w161
    (by decide +kernel) w195_sound w195_sound w161_sound) (by decide +kernel)
lemma B5_1_2Raw_4_0_0 : (B5_1_2Raw (shape 4 0 0)).Encloses (splitWeight positiveSecond tablep (shape 5 1 2) (shape 4 0 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 5 1 2) (shape 4 0 0)
    (-32128) (0) (-5727) w66 w195 w161
    (by decide +kernel) w66_sound w195_sound w161_sound) (by decide +kernel)
lemma B5_1_2Raw_sound (u : Shape) (hu : u ∈ below (shape 5 1 2)) :
    (B5_1_2Raw u).Encloses (splitWeight positiveSecond tablep (shape 5 1 2) u : ℝ) := by
  rw [B5_1_2_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · exact B5_1_2Raw_1_1_2
  · exact B5_1_2Raw_2_0_2
  · exact B5_1_2Raw_2_1_1
  · exact B5_1_2Raw_3_0_1
  · exact B5_1_2Raw_3_1_0
  · exact B5_1_2Raw_4_0_0
lemma B5_1_2Den_sound : B5_1_2Den.Encloses (((below (shape 5 1 2)).map (splitWeight positiveSecond tablep (shape 5 1 2))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (below (shape 5 1 2)) B5_1_2Raw (splitWeight positiveSecond tablep (shape 5 1 2)) B5_1_2Raw_sound) (by decide +kernel)
lemma B5_1_2Den_positive : 0 < B5_1_2Den.lower := by decide +kernel
lemma B5_1_2Law_check_1_1_2 : contains (.mul (B5_1_2Raw (shape 1 1 2)) (.inv B5_1_2Den)) (B5_1_2Table (shape 1 1 2)) = true := by decide +kernel
lemma B5_1_2Law_check_2_0_2 : contains (.mul (B5_1_2Raw (shape 2 0 2)) (.inv B5_1_2Den)) (B5_1_2Table (shape 2 0 2)) = true := by decide +kernel
lemma B5_1_2Law_check_2_1_1 : contains (.mul (B5_1_2Raw (shape 2 1 1)) (.inv B5_1_2Den)) (B5_1_2Table (shape 2 1 1)) = true := by decide +kernel
lemma B5_1_2Law_check_3_0_1 : contains (.mul (B5_1_2Raw (shape 3 0 1)) (.inv B5_1_2Den)) (B5_1_2Table (shape 3 0 1)) = true := by decide +kernel
lemma B5_1_2Law_check_3_1_0 : contains (.mul (B5_1_2Raw (shape 3 1 0)) (.inv B5_1_2Den)) (B5_1_2Table (shape 3 1 0)) = true := by decide +kernel
lemma B5_1_2Law_check_4_0_0 : contains (.mul (B5_1_2Raw (shape 4 0 0)) (.inv B5_1_2Den)) (B5_1_2Table (shape 4 0 0)) = true := by decide +kernel
lemma B5_1_2Law_check (u : Shape) (hu : u ∈ below (shape 5 1 2)) :
    contains (.mul (B5_1_2Raw u) (.inv B5_1_2Den)) (B5_1_2Table u) = true := by
  rw [B5_1_2_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · exact B5_1_2Law_check_1_1_2
  · exact B5_1_2Law_check_2_0_2
  · exact B5_1_2Law_check_2_1_1
  · exact B5_1_2Law_check_3_0_1
  · exact B5_1_2Law_check_3_1_0
  · exact B5_1_2Law_check_4_0_0
lemma B5_1_2Law_sound (u : Shape) :
    (B5_1_2Law u).Encloses (stageBLaw (shape 5 1 2) u : ℝ) := by
  by_cases hu : u ∈ below (shape 5 1 2)
  · have h := contains_sound (Ball.mul_sound (B5_1_2Raw_sound u hu)
      (Ball.inv_sound B5_1_2Den_sound B5_1_2Den_positive)) (B5_1_2Law_check u hu)
    simpa only [B5_1_2Law, hu, ite_true, if_true, stageBLaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [B5_1_2Law, hu, ite_false, if_false, stageBLaw, splitLaw, Rat.cast_zero]
    simpa only [Rat.cast_zero] using Ball.exact_sound 0

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal1_1_6
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
lemma second_5_1_2 : (secondProbs (shape 5 1 2)).Encloses (secondMass (shape 5 1 2) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 5 1 2))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 5 1 2))))
  · decide +kernel

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal5_1_2
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.bWeight_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inr _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inr
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
lemma B5_1_2U1_1_2Leaf_sound : B5_1_2U1_1_2Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 5 1 2) (shape 1 1 2)) := by
  have hh : shapeMax (shape 1 1 2) = 2 := by decide +kernel
  have hp : positive (shape 1 1 2) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, if_false]
  have ht : (Ball.exact (1957953 / 1000000)).Encloses (2 - (binaryParameter (shape 5 1 2) (shape 1 1 2) : ℝ)) := by
    have he : binaryParameter (shape 5 1 2) (shape 1 1 2) = (42047 / 1000000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((1957953 / 1000000) : ℚ) using 1
    all_goals try with_reducible_and_instances rfl
    norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
lemma B5_1_2U1_1_2Mass_sound : B5_1_2U1_1_2Mass.Encloses (littleMass (shape 5 1 2) (shape 1 1 2) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_5_1_2))
    (B5_1_2Law_sound (shape 1 1 2))) (by decide +kernel)
lemma B5_1_2U2_0_2D_sound : B5_1_2U2_0_2D.Encloses (binaryParameter (shape 5 1 2) (shape 2 0 2) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
lemma B5_1_2U2_0_2OneD_sound : B5_1_2U2_0_2OneD.Encloses (1 - (binaryParameter (shape 5 1 2) (shape 2 0 2) : ℝ)) := by
  have he : binaryParameter (shape 5 1 2) (shape 2 0 2) = (6867 / 62500) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((55633 / 62500) : ℚ) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [B5_1_2U2_0_2OneD, Ball.exact])
lemma B5_1_2U2_0_2EDLog_sound : B5_1_2U2_0_2EDLog.Encloses (Real.log ((binaryParameter (shape 5 1 2) (shape 2 0 2) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B5_1_2U2_0_2D_sound) (w := B5_1_2U2_0_2EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma B5_1_2U2_0_2ED_sound : B5_1_2U2_0_2ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 5 1 2) (shape 2 0 2) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B5_1_2U2_0_2D_sound) B5_1_2U2_0_2EDLog_sound) (by decide +kernel)
lemma B5_1_2U2_0_2EOneDLog_sound : B5_1_2U2_0_2EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 5 1 2) (shape 2 0 2) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B5_1_2U2_0_2OneD_sound) (w := B5_1_2U2_0_2EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma B5_1_2U2_0_2EOneD_sound : B5_1_2U2_0_2EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 5 1 2) (shape 2 0 2) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B5_1_2U2_0_2OneD_sound) B5_1_2U2_0_2EOneDLog_sound) (by decide +kernel)
lemma B5_1_2U2_0_2BinaryEntropy_sound : B5_1_2U2_0_2BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 5 1 2) (shape 2 0 2))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B5_1_2U2_0_2EOneD_sound B5_1_2U2_0_2ED_sound)
    (Ball.mul_sound B5_1_2U2_0_2D_sound logN2_sound)) (by decide +kernel)
lemma B5_1_2U2_0_2Leaf_sound : B5_1_2U2_0_2Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 5 1 2) (shape 2 0 2)) := by
  have hh : shapeMax (shape 2 0 2) = 2 := by decide +kernel
  have hp : positive (shape 2 0 2) = false := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_false,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, if_false, ite_true, if_true]
  exact contains_sound (Ball.add_sound B5_1_2U2_0_2BinaryEntropy_sound
    (Ball.mul_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      B5_1_2U2_0_2OneD_sound) logN5_sound)) (by decide +kernel)
lemma B5_1_2U2_0_2Mass_sound : B5_1_2U2_0_2Mass.Encloses (littleMass (shape 5 1 2) (shape 2 0 2) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_5_1_2))
    (B5_1_2Law_sound (shape 2 0 2))) (by decide +kernel)
lemma B5_1_2U2_1_1Leaf_sound : B5_1_2U2_1_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 5 1 2) (shape 2 1 1)) := by
  have hh : shapeMax (shape 2 1 1) = 2 := by decide +kernel
  have hp : positive (shape 2 1 1) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, if_false]
  have ht : (Ball.exact (998007 / 500000)).Encloses (2 - (binaryParameter (shape 5 1 2) (shape 2 1 1) : ℝ)) := by
    have he : binaryParameter (shape 5 1 2) (shape 2 1 1) = (1993 / 500000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((998007 / 500000) : ℚ) using 1
    all_goals try with_reducible_and_instances rfl
    norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
lemma B5_1_2U2_1_1Mass_sound : B5_1_2U2_1_1Mass.Encloses (littleMass (shape 5 1 2) (shape 2 1 1) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_5_1_2))
    (B5_1_2Law_sound (shape 2 1 1))) (by decide +kernel)
lemma B5_1_2U3_0_1Leaf_sound : B5_1_2U3_0_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 5 1 2) (shape 3 0 1)) := by
  have hh : shapeMax (shape 3 0 1) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, if_false, ite_true, if_true]
  exact logN10_sound
lemma B5_1_2U3_0_1Mass_sound : B5_1_2U3_0_1Mass.Encloses (littleMass (shape 5 1 2) (shape 3 0 1) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_5_1_2))
    (B5_1_2Law_sound (shape 3 0 1))) (by decide +kernel)
lemma B5_1_2U3_1_0Leaf_sound : B5_1_2U3_1_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 5 1 2) (shape 3 1 0)) := by
  have hh : shapeMax (shape 3 1 0) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, if_false, ite_true, if_true]
  exact logN10_sound
lemma B5_1_2U3_1_0Mass_sound : B5_1_2U3_1_0Mass.Encloses (littleMass (shape 5 1 2) (shape 3 1 0) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_5_1_2))
    (B5_1_2Law_sound (shape 3 1 0))) (by decide +kernel)
lemma B5_1_2U4_0_0Leaf_sound : B5_1_2U4_0_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 5 1 2) (shape 4 0 0)) := by
  have hh : shapeMax (shape 4 0 0) = 4 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, ite_true, if_true]
  simpa only [Rat.cast_zero, B5_1_2U4_0_0Leaf, Ball.exact] using Ball.exact_sound 0
lemma B5_1_2U4_0_0Mass_sound : B5_1_2U4_0_0Mass.Encloses (littleMass (shape 5 1 2) (shape 4 0 0) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_5_1_2))
    (B5_1_2Law_sound (shape 4 0 0))) (by decide +kernel)
lemma B5_1_2Leaves_sound (u : Shape) (hu : u ∈ below (shape 5 1 2)) :
    (B5_1_2Leaves u).Encloses (AllFieldTerminalRates.secondLeafRate (shape 5 1 2) u) := by
  rw [B5_1_2_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · exact B5_1_2U1_1_2Leaf_sound
  · exact B5_1_2U2_0_2Leaf_sound
  · exact B5_1_2U2_1_1Leaf_sound
  · exact B5_1_2U3_0_1Leaf_sound
  · exact B5_1_2U3_1_0Leaf_sound
  · exact B5_1_2U4_0_0Leaf_sound
lemma B5_1_2Masses_sound (u : Shape) (hu : u ∈ below (shape 5 1 2)) :
    (B5_1_2Masses u).Encloses ((fun u => (littleMass (shape 5 1 2) u : ℝ)) u) := by
  rw [B5_1_2_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · exact B5_1_2U1_1_2Mass_sound
  · exact B5_1_2U2_0_2Mass_sound
  · exact B5_1_2U2_1_1Mass_sound
  · exact B5_1_2U3_0_1Mass_sound
  · exact B5_1_2U3_1_0Mass_sound
  · exact B5_1_2U4_0_0Mass_sound
lemma B5_1_2S2_sound_oai : B5_1_2S2.Encloses
    (((below (shape 5 1 2)).map fun u => (littleMass (shape 5 1 2) u : ℝ) * AllFieldTerminalRates.secondLeafRate (shape 5 1 2) u).sum) := by
  exact contains_sound (listSumBall_sound (below (shape 5 1 2))
    (fun u => .mul (B5_1_2Masses u) (B5_1_2Leaves u)) _
    (fun u hu => Ball.mul_sound (B5_1_2Masses_sound u hu) (B5_1_2Leaves_sound u hu))) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B5_1_2S2_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B5_1_2S2_sound_oai
