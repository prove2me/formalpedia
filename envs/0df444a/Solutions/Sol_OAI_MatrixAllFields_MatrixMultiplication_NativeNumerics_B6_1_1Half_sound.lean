-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B6_1_1Half_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:59:16.401798+00:00
-- url     : https://prove2.me/submissions/941042be-80ae-4309-9d5f-a7a3daf45671

import Mathlib
import Definitions.Def_OAIQ254M007
import Definitions.Def_OAIQ254M010
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_inv_sound
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

lemma forall_fin3 {P : Fin 3 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) : ∀ i, P i := by
  intro i
  fin_cases i <;> assumption

lemma exact_rat_enclosed {q r : ℚ} (h : q = r) : (Ball.exact q).Encloses (r : ℝ) := by
  rw [h]
  exact Ball.exact_sound r

lemma pairLawBall_sound {A : Type*} [Fintype A] (support : List Shape) (s : Shape)
    (bs : Shape → Ball) (p : Shape → ℝ) (bq : Shape → A → Ball) (q : Shape → A → ℝ)
    (hp : ∀ u ∈ support, (bs u).Encloses (p u))
    (hq : ∀ u a, (bq u a).Encloses (q u a)) (ij : A × A) :
    (pairLawBall support s bs bq ij).Encloses (pairLaw support s p q ij) := by
  apply listSumBall_sound
  intro u hu
  exact Ball.mul_sound (Ball.mul_sound (hp u hu) (hq u ij.1)) (hq _ ij.2)

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
lemma w193_sound : w193.Encloses (weight (-122) : ℝ) := by
  exact weight_enclosed_of_trace (-122) w193Trace w193S0 w193S1 w193S2 w193S3 w193S4 w193S5
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
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_NativeInterior
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
open AllFieldInitialEntropyCertificate
open scoped BigOperators
lemma B6_1_1_below : below (shape 6 1 1) = [
  (shape 2 1 1),
  (shape 3 0 1),
  (shape 3 1 0),
  (shape 4 0 0)] := by decide +kernel
lemma B6_1_1Raw_2_1_1 : (B6_1_1Raw (shape 2 1 1)).Encloses (splitWeight positiveSecond tablep (shape 6 1 1) (shape 2 1 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 6 1 1) (shape 2 1 1)
    (-122) (0) (0) w193 w195 w195
    (by decide +kernel) w193_sound w195_sound w195_sound) (by decide +kernel)
lemma B6_1_1Raw_3_0_1 : (B6_1_1Raw (shape 3 0 1)).Encloses (splitWeight positiveSecond tablep (shape 6 1 1) (shape 3 0 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 6 1 1) (shape 3 0 1)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma B6_1_1Raw_3_1_0 : (B6_1_1Raw (shape 3 1 0)).Encloses (splitWeight positiveSecond tablep (shape 6 1 1) (shape 3 1 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 6 1 1) (shape 3 1 0)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma B6_1_1Raw_4_0_0 : (B6_1_1Raw (shape 4 0 0)).Encloses (splitWeight positiveSecond tablep (shape 6 1 1) (shape 4 0 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 6 1 1) (shape 4 0 0)
    (-122) (0) (0) w193 w195 w195
    (by decide +kernel) w193_sound w195_sound w195_sound) (by decide +kernel)
lemma B6_1_1Raw_sound (u : Shape) (hu : u ∈ below (shape 6 1 1)) :
    (B6_1_1Raw u).Encloses (splitWeight positiveSecond tablep (shape 6 1 1) u : ℝ) := by
  rw [B6_1_1_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl
  · exact B6_1_1Raw_2_1_1
  · exact B6_1_1Raw_3_0_1
  · exact B6_1_1Raw_3_1_0
  · exact B6_1_1Raw_4_0_0
lemma B6_1_1Den_sound : B6_1_1Den.Encloses (((below (shape 6 1 1)).map (splitWeight positiveSecond tablep (shape 6 1 1))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (below (shape 6 1 1)) B6_1_1Raw (splitWeight positiveSecond tablep (shape 6 1 1)) B6_1_1Raw_sound) (by decide +kernel)
lemma B6_1_1Den_positive : 0 < B6_1_1Den.lower := by decide +kernel
lemma B6_1_1Law_check_2_1_1 : contains (.mul (B6_1_1Raw (shape 2 1 1)) (.inv B6_1_1Den)) (B6_1_1Table (shape 2 1 1)) = true := by decide +kernel
lemma B6_1_1Law_check_3_0_1 : contains (.mul (B6_1_1Raw (shape 3 0 1)) (.inv B6_1_1Den)) (B6_1_1Table (shape 3 0 1)) = true := by decide +kernel
lemma B6_1_1Law_check_3_1_0 : contains (.mul (B6_1_1Raw (shape 3 1 0)) (.inv B6_1_1Den)) (B6_1_1Table (shape 3 1 0)) = true := by decide +kernel
lemma B6_1_1Law_check_4_0_0 : contains (.mul (B6_1_1Raw (shape 4 0 0)) (.inv B6_1_1Den)) (B6_1_1Table (shape 4 0 0)) = true := by decide +kernel
lemma B6_1_1Law_check (u : Shape) (hu : u ∈ below (shape 6 1 1)) :
    contains (.mul (B6_1_1Raw u) (.inv B6_1_1Den)) (B6_1_1Table u) = true := by
  rw [B6_1_1_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl
  · exact B6_1_1Law_check_2_1_1
  · exact B6_1_1Law_check_3_0_1
  · exact B6_1_1Law_check_3_1_0
  · exact B6_1_1Law_check_4_0_0
lemma B6_1_1Law_sound (u : Shape) :
    (B6_1_1Law u).Encloses (stageBLaw (shape 6 1 1) u : ℝ) := by
  by_cases hu : u ∈ below (shape 6 1 1)
  · have h := contains_sound (Ball.mul_sound (B6_1_1Raw_sound u hu)
      (Ball.inv_sound B6_1_1Den_sound B6_1_1Den_positive)) (B6_1_1Law_check u hu)
    simpa only [B6_1_1Law, hu, ite_true, if_true, stageBLaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [B6_1_1Law, hu, ite_false, if_false, stageBLaw, splitLaw, Rat.cast_zero]
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
lemma B6_1_1Binary_eq (u : Shape) (hu : u ∈ shapes 4) :
    binaryParameter (shape 6 1 1) u = B6_1_1Binary u := by
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

lemma B6_1_1Little_sound (u : Shape) (w : Fin 3) (i : Fin 6) :
    (B6_1_1Little u w i).Encloses (littleLaw (shape 6 1 1) u w i : ℝ) := by
  by_cases hu : u ∈ shapes 4
  · simp only [B6_1_1Little, hu, ite_true, if_true]
    apply exact_rat_enclosed
    simp only [B6_1_1LittleRat, littleLaw, B6_1_1Binary_eq u hu]
  · simp only [B6_1_1Little, hu, ite_false, if_false]
    exact Ball.exact_sound _
lemma B6_1_1Half_check_0_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 6 1 1)) (shape 6 1 1) B6_1_1Law
      (fun u => B6_1_1Little u 0) ((0 : Fin 6),j)) (B6_1_1Half 0 (0,j)) = true := by
  decide +kernel
lemma B6_1_1Half_check_0_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 6 1 1)) (shape 6 1 1) B6_1_1Law
      (fun u => B6_1_1Little u 0) ((1 : Fin 6),j)) (B6_1_1Half 0 (1,j)) = true := by
  decide +kernel
lemma B6_1_1Half_check_0_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 6 1 1)) (shape 6 1 1) B6_1_1Law
      (fun u => B6_1_1Little u 0) ((2 : Fin 6),j)) (B6_1_1Half 0 (2,j)) = true := by
  decide +kernel
lemma B6_1_1Half_check_0_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 6 1 1)) (shape 6 1 1) B6_1_1Law
      (fun u => B6_1_1Little u 0) ((3 : Fin 6),j)) (B6_1_1Half 0 (3,j)) = true := by
  decide +kernel
lemma B6_1_1Half_check_0_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 6 1 1)) (shape 6 1 1) B6_1_1Law
      (fun u => B6_1_1Little u 0) ((4 : Fin 6),j)) (B6_1_1Half 0 (4,j)) = true := by
  decide +kernel
lemma B6_1_1Half_check_0_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 6 1 1)) (shape 6 1 1) B6_1_1Law
      (fun u => B6_1_1Little u 0) ((5 : Fin 6),j)) (B6_1_1Half 0 (5,j)) = true := by
  decide +kernel
lemma B6_1_1Half_check_1_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 6 1 1)) (shape 6 1 1) B6_1_1Law
      (fun u => B6_1_1Little u 1) ((0 : Fin 6),j)) (B6_1_1Half 1 (0,j)) = true := by
  decide +kernel
lemma B6_1_1Half_check_1_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 6 1 1)) (shape 6 1 1) B6_1_1Law
      (fun u => B6_1_1Little u 1) ((1 : Fin 6),j)) (B6_1_1Half 1 (1,j)) = true := by
  decide +kernel
lemma B6_1_1Half_check_1_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 6 1 1)) (shape 6 1 1) B6_1_1Law
      (fun u => B6_1_1Little u 1) ((2 : Fin 6),j)) (B6_1_1Half 1 (2,j)) = true := by
  decide +kernel
lemma B6_1_1Half_check_1_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 6 1 1)) (shape 6 1 1) B6_1_1Law
      (fun u => B6_1_1Little u 1) ((3 : Fin 6),j)) (B6_1_1Half 1 (3,j)) = true := by
  decide +kernel
lemma B6_1_1Half_check_1_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 6 1 1)) (shape 6 1 1) B6_1_1Law
      (fun u => B6_1_1Little u 1) ((4 : Fin 6),j)) (B6_1_1Half 1 (4,j)) = true := by
  decide +kernel
lemma B6_1_1Half_check_1_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 6 1 1)) (shape 6 1 1) B6_1_1Law
      (fun u => B6_1_1Little u 1) ((5 : Fin 6),j)) (B6_1_1Half 1 (5,j)) = true := by
  decide +kernel
lemma B6_1_1Half_check_2_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 6 1 1)) (shape 6 1 1) B6_1_1Law
      (fun u => B6_1_1Little u 2) ((0 : Fin 6),j)) (B6_1_1Half 2 (0,j)) = true := by
  decide +kernel
lemma B6_1_1Half_check_2_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 6 1 1)) (shape 6 1 1) B6_1_1Law
      (fun u => B6_1_1Little u 2) ((1 : Fin 6),j)) (B6_1_1Half 2 (1,j)) = true := by
  decide +kernel
lemma B6_1_1Half_check_2_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 6 1 1)) (shape 6 1 1) B6_1_1Law
      (fun u => B6_1_1Little u 2) ((2 : Fin 6),j)) (B6_1_1Half 2 (2,j)) = true := by
  decide +kernel
lemma B6_1_1Half_check_2_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 6 1 1)) (shape 6 1 1) B6_1_1Law
      (fun u => B6_1_1Little u 2) ((3 : Fin 6),j)) (B6_1_1Half 2 (3,j)) = true := by
  decide +kernel
lemma B6_1_1Half_check_2_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 6 1 1)) (shape 6 1 1) B6_1_1Law
      (fun u => B6_1_1Little u 2) ((4 : Fin 6),j)) (B6_1_1Half 2 (4,j)) = true := by
  decide +kernel
lemma B6_1_1Half_check_2_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 6 1 1)) (shape 6 1 1) B6_1_1Law
      (fun u => B6_1_1Little u 2) ((5 : Fin 6),j)) (B6_1_1Half 2 (5,j)) = true := by
  decide +kernel
lemma B6_1_1Half_sound_oai (w : Fin 3) (ij : PairSlot) :
    (B6_1_1Half w ij).Encloses (halfLaw (shape 6 1 1) w ij : ℝ) := by
  have hcheck : contains (pairLawBall (below (shape 6 1 1)) (shape 6 1 1) B6_1_1Law
      (fun u => B6_1_1Little u w) ij) (B6_1_1Half w ij) = true := by
    rcases ij with ⟨i,j⟩
    revert i w
    apply forall_fin3
    · exact forall_fin6 (B6_1_1Half_check_0_0 j) (B6_1_1Half_check_0_1 j) (B6_1_1Half_check_0_2 j) (B6_1_1Half_check_0_3 j) (B6_1_1Half_check_0_4 j) (B6_1_1Half_check_0_5 j)
    · exact forall_fin6 (B6_1_1Half_check_1_0 j) (B6_1_1Half_check_1_1 j) (B6_1_1Half_check_1_2 j) (B6_1_1Half_check_1_3 j) (B6_1_1Half_check_1_4 j) (B6_1_1Half_check_1_5 j)
    · exact forall_fin6 (B6_1_1Half_check_2_0 j) (B6_1_1Half_check_2_1 j) (B6_1_1Half_check_2_2 j) (B6_1_1Half_check_2_3 j) (B6_1_1Half_check_2_4 j) (B6_1_1Half_check_2_5 j)
  have h := contains_sound (pairLawBall_sound (below (shape 6 1 1)) (shape 6 1 1)
    B6_1_1Law (fun u => (stageBLaw (shape 6 1 1) u : ℝ))
    (fun u => B6_1_1Little u w) (fun u i => (littleLaw (shape 6 1 1) u w i : ℝ))
    (fun u _ => B6_1_1Law_sound u) (fun u i => B6_1_1Little_sound u w i) ij) hcheck
  have hp : positive (shape 6 1 1) = true := by decide +kernel
  simpa only [halfLaw, hp, ite_true, if_true, pairLaw, positiveHalfLaw, Rat.cast_list_sum,
    List.map_map, Function.comp_def, Rat.cast_mul] using h

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B6_1_1Half_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B6_1_1Half_sound_oai
