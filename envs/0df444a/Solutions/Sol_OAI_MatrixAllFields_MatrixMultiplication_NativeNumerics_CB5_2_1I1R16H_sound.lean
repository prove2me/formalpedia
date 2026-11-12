-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB5_2_1I1R16H_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:19:34.976387+00:00
-- url     : https://prove2.me/submissions/2f01f46b-a1ae-40a8-ba3a-5539222e180f

import Mathlib
import Definitions.Def_OAIQ254M006
import Definitions.Def_OAIQ254M011
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_inv_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_mul_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkPolynomial_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_finSumBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_CompactCertificate_entropyLookup_sound
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
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
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

lemma exact_rat_enclosed {q r : ℚ} (h : q = r) : (Ball.exact q).Encloses (r : ℝ) := by
  rw [h]
  exact Ball.exact_sound r

lemma entropyFin_enclosed (n : ℕ) (p : Fin n → ℝ) (bs : Fin n → Ball)
    (h : ∀ i, (bs i).Encloses (Foundation.entropyTerm (p i))) :
    (finSumBall n bs).Encloses (Foundation.finiteEntropy p) :=
  finSumBall_sound n _ _ h

lemma residualBall_sound_on {A : Type*} [Fintype A] (support : List Shape)
    (bs : Shape → Ball) (p : Shape → ℝ) (priority : Placement) (position : Fin 3)
    (bq : Shape → A → Ball) (q : Shape → A → ℝ)
    (hp : ∀ u ∈ support, (bs u).Encloses (p u))
    (hq : ∀ u ∈ support, ∀ a, (bq u a).Encloses (q u a)) (k : Fin 17) (a : A) :
    (residualBall support bs priority position bq k a).Encloses
      (residualLaw support p priority position q k a) := by
  apply listSumBall_sound
  intro u hu
  by_cases hk : ¬ designated priority position u ∧ u (priority position) = k.val
  · simpa only [ite_eq_left hk] using Ball.mul_sound (hp u hu) (hq u hu a)
  · simpa only [hk, ite_false, if_false, Rat.cast_zero] using Ball.exact_sound 0

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
lemma w65_sound : w65.Encloses (weight (-32138) : ℝ) := by
  exact weight_enclosed_of_trace (-32138) w65Trace w65S0 w65S1 w65S2 w65S3 w65S4 w65S5
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
lemma w162_sound : w162.Encloses (weight (-5725) : ℝ) := by
  exact weight_enclosed_of_trace (-5725) w162Trace w162S0 w162S1 w162S2 w162S3 w162S4 w162S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_LittleB1_3_4
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
lemma shapes4_list : shapes 4 = [
  (shape 0 0 4),
  (shape 0 1 3),
  (shape 0 2 2),
  (shape 0 3 1),
  (shape 0 4 0),
  (shape 1 0 3),
  (shape 1 1 2),
  (shape 1 2 1),
  (shape 1 3 0),
  (shape 2 0 2),
  (shape 2 1 1),
  (shape 2 2 0),
  (shape 3 0 1),
  (shape 3 1 0),
  (shape 4 0 0)] := by decide +kernel

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal5_2_1
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
lemma B5_2_1_below : below (shape 5 2 1) = [
  (shape 1 2 1),
  (shape 2 1 1),
  (shape 2 2 0),
  (shape 3 0 1),
  (shape 3 1 0),
  (shape 4 0 0)] := by decide +kernel
lemma B5_2_1Raw_1_2_1 : (B5_2_1Raw (shape 1 2 1)).Encloses (splitWeight positiveSecond tablep (shape 5 2 1) (shape 1 2 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 5 2 1) (shape 1 2 1)
    (-32138) (-5725) (0) w65 w162 w195
    (by decide +kernel) w65_sound w162_sound w195_sound) (by decide +kernel)
lemma B5_2_1Raw_2_1_1 : (B5_2_1Raw (shape 2 1 1)).Encloses (splitWeight positiveSecond tablep (shape 5 2 1) (shape 2 1 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 5 2 1) (shape 2 1 1)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma B5_2_1Raw_2_2_0 : (B5_2_1Raw (shape 2 2 0)).Encloses (splitWeight positiveSecond tablep (shape 5 2 1) (shape 2 2 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 5 2 1) (shape 2 2 0)
    (0) (-5725) (0) w195 w162 w195
    (by decide +kernel) w195_sound w162_sound w195_sound) (by decide +kernel)
lemma B5_2_1Raw_3_0_1 : (B5_2_1Raw (shape 3 0 1)).Encloses (splitWeight positiveSecond tablep (shape 5 2 1) (shape 3 0 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 5 2 1) (shape 3 0 1)
    (0) (-5725) (0) w195 w162 w195
    (by decide +kernel) w195_sound w162_sound w195_sound) (by decide +kernel)
lemma B5_2_1Raw_3_1_0 : (B5_2_1Raw (shape 3 1 0)).Encloses (splitWeight positiveSecond tablep (shape 5 2 1) (shape 3 1 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 5 2 1) (shape 3 1 0)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma B5_2_1Raw_4_0_0 : (B5_2_1Raw (shape 4 0 0)).Encloses (splitWeight positiveSecond tablep (shape 5 2 1) (shape 4 0 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 5 2 1) (shape 4 0 0)
    (-32138) (-5725) (0) w65 w162 w195
    (by decide +kernel) w65_sound w162_sound w195_sound) (by decide +kernel)
lemma B5_2_1Raw_sound (u : Shape) (hu : u ∈ below (shape 5 2 1)) :
    (B5_2_1Raw u).Encloses (splitWeight positiveSecond tablep (shape 5 2 1) u : ℝ) := by
  rw [B5_2_1_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · exact B5_2_1Raw_1_2_1
  · exact B5_2_1Raw_2_1_1
  · exact B5_2_1Raw_2_2_0
  · exact B5_2_1Raw_3_0_1
  · exact B5_2_1Raw_3_1_0
  · exact B5_2_1Raw_4_0_0
lemma B5_2_1Den_sound : B5_2_1Den.Encloses (((below (shape 5 2 1)).map (splitWeight positiveSecond tablep (shape 5 2 1))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (below (shape 5 2 1)) B5_2_1Raw (splitWeight positiveSecond tablep (shape 5 2 1)) B5_2_1Raw_sound) (by decide +kernel)
lemma B5_2_1Den_positive : 0 < B5_2_1Den.lower := by decide +kernel
lemma B5_2_1Law_check_1_2_1 : contains (.mul (B5_2_1Raw (shape 1 2 1)) (.inv B5_2_1Den)) (B5_2_1Table (shape 1 2 1)) = true := by decide +kernel
lemma B5_2_1Law_check_2_1_1 : contains (.mul (B5_2_1Raw (shape 2 1 1)) (.inv B5_2_1Den)) (B5_2_1Table (shape 2 1 1)) = true := by decide +kernel
lemma B5_2_1Law_check_2_2_0 : contains (.mul (B5_2_1Raw (shape 2 2 0)) (.inv B5_2_1Den)) (B5_2_1Table (shape 2 2 0)) = true := by decide +kernel
lemma B5_2_1Law_check_3_0_1 : contains (.mul (B5_2_1Raw (shape 3 0 1)) (.inv B5_2_1Den)) (B5_2_1Table (shape 3 0 1)) = true := by decide +kernel
lemma B5_2_1Law_check_3_1_0 : contains (.mul (B5_2_1Raw (shape 3 1 0)) (.inv B5_2_1Den)) (B5_2_1Table (shape 3 1 0)) = true := by decide +kernel
lemma B5_2_1Law_check_4_0_0 : contains (.mul (B5_2_1Raw (shape 4 0 0)) (.inv B5_2_1Den)) (B5_2_1Table (shape 4 0 0)) = true := by decide +kernel
lemma B5_2_1Law_check (u : Shape) (hu : u ∈ below (shape 5 2 1)) :
    contains (.mul (B5_2_1Raw u) (.inv B5_2_1Den)) (B5_2_1Table u) = true := by
  rw [B5_2_1_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · exact B5_2_1Law_check_1_2_1
  · exact B5_2_1Law_check_2_1_1
  · exact B5_2_1Law_check_2_2_0
  · exact B5_2_1Law_check_3_0_1
  · exact B5_2_1Law_check_3_1_0
  · exact B5_2_1Law_check_4_0_0
lemma B5_2_1Law_sound (u : Shape) :
    (B5_2_1Law u).Encloses (stageBLaw (shape 5 2 1) u : ℝ) := by
  by_cases hu : u ∈ below (shape 5 2 1)
  · have h := contains_sound (Ball.mul_sound (B5_2_1Raw_sound u hu)
      (Ball.inv_sound B5_2_1Den_sound B5_2_1Den_positive)) (B5_2_1Law_check u hu)
    simpa only [B5_2_1Law, hu, ite_true, if_true, stageBLaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [B5_2_1Law, hu, ite_false, if_false, stageBLaw, splitLaw, Rat.cast_zero]
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
lemma B5_2_1Binary_eq (u : Shape) (hu : u ∈ shapes 4) :
    binaryParameter (shape 5 2 1) u = B5_2_1Binary u := by
  rw [shapes4_list] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

lemma B5_2_1Little_sound (u : Shape) (w : Fin 3) (i : Fin 6) :
    (B5_2_1Little u w i).Encloses (littleLaw (shape 5 2 1) u w i : ℝ) := by
  by_cases hu : u ∈ shapes 4
  · simp only [B5_2_1Little, hu, ite_true, if_true]
    apply exact_rat_enclosed
    simp only [B5_2_1LittleRat, littleLaw, B5_2_1Binary_eq u hu]
  · simp only [B5_2_1Little, hu, ite_false, if_false]
    exact Ball.exact_sound _

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB5_2_1I1
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
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
lemma CB5_2_1I1R16Raw_sound (a : Fin 6) :
    (CB5_2_1I1R16Raw a).Encloses (CB5_2_1I1R16Value a) := by
  exact residualBall_sound_on (below (shape 5 2 1)) B5_2_1Law (fun u => (stageBLaw (shape 5 2 1) u : ℝ)) (stageBPriority (shape 5 2 1)) 1 (fun u => B5_2_1Little u ((stageBPriority (shape 5 2 1)) 1)) (fun u a => (littleLaw (shape 5 2 1) u ((stageBPriority (shape 5 2 1)) 1) a : ℝ)) (fun u _ => B5_2_1Law_sound u) (fun u _ a => B5_2_1Little_sound u ((stageBPriority (shape 5 2 1)) 1) a) 16 a
lemma CB5_2_1I1R16Certificates_valid :
    CB5_2_1I1R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB5_2_1I1R16P_check : ∀ a : Fin 6, contains (CB5_2_1I1R16Raw a) (CB5_2_1I1R16P a) = true := by
  decide +kernel
lemma CB5_2_1I1R16P_sound (a : Fin 6) :
    (CB5_2_1I1R16P a).Encloses (CB5_2_1I1R16Value a) :=
  contains_sound (CB5_2_1I1R16Raw_sound a) (CB5_2_1I1R16P_check a)
lemma CB5_2_1I1R16Terms_sound (a : Fin 6) :
    (CB5_2_1I1R16Terms a).Encloses (Foundation.entropyTerm (CB5_2_1I1R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB5_2_1I1R16Certificates_valid
    (CB5_2_1I1R16CertificateIndex a) (CB5_2_1I1R16P_sound a)
lemma CB5_2_1I1R16Entropy_sound : CB5_2_1I1R16Entropy.Encloses (Foundation.finiteEntropy CB5_2_1I1R16Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB5_2_1I1R16Value CB5_2_1I1R16Terms CB5_2_1I1R16Terms_sound) (by decide +kernel)
lemma CB5_2_1I1R16Mass_sound : CB5_2_1I1R16Mass.Encloses (∑ a, CB5_2_1I1R16Value a) := by
  exact contains_sound (finSumBall_sound 6 CB5_2_1I1R16P CB5_2_1I1R16Value CB5_2_1I1R16P_sound) (by decide +kernel)
lemma CB5_2_1I1R16MassTerm_sound : CB5_2_1I1R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB5_2_1I1R16Value a))) :=
  entropyTerm_zero_ball (CB5_2_1I1R16Mass_sound)
lemma CB5_2_1I1R16H_sound_oai : CB5_2_1I1R16H.Encloses (homogeneousEntropy CB5_2_1I1R16Value) := by
  exact contains_sound (homogeneous_enclosed CB5_2_1I1R16Value CB5_2_1I1R16MassTerm_sound CB5_2_1I1R16Entropy_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB5_2_1I1R16H_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB5_2_1I1R16H_sound_oai
