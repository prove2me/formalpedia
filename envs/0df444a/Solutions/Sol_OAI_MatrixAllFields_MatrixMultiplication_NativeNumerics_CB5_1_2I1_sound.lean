-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB5_1_2I1_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:18:18.351062+00:00
-- url     : https://prove2.me/submissions/7237a591-0881-4305-b4bf-af5c691f2aac

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
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_CompactCertificate_entropyLookup_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB5_1_2I1R10H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB5_1_2I1R11H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB5_1_2I1R12H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB5_1_2I1R13H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB5_1_2I1R14H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_entropyTerm_ball
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

theorem neg_sound {a : Ball} {x : ℝ} (hx : a.Encloses x) :
    (neg a).Encloses (-x) := by
  simpa only [Encloses, neg, Rat.cast_neg, neg_sub_neg, abs_sub_comm] using hx

end Ball

end MatrixMultiplication.AllFieldCertificates

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SparseContraction
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
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

lemma exact_rat_enclosed {q r : ℚ} (h : q = r) : (Ball.exact q).Encloses (r : ℝ) := by
  rw [h]
  exact Ball.exact_sound r

lemma pairSumBall_sound (bs : PairSlot → Ball) (v : PairSlot → ℝ)
    (h : ∀ a, (bs a).Encloses (v a)) :
    (pairSumBall bs).Encloses (∑ a, v a) := by
  exact product_fin6_enclosed _ _ (fun i j => h (i,j))

lemma entropyFin_enclosed (n : ℕ) (p : Fin n → ℝ) (bs : Fin n → Ball)
    (h : ∀ i, (bs i).Encloses (Foundation.entropyTerm (p i))) :
    (finSumBall n bs).Encloses (Foundation.finiteEntropy p) :=
  finSumBall_sound n _ _ h

lemma entropyPair_enclosed (p : PairSlot → ℝ) (bs : PairSlot → Ball)
    (h : ∀ i, (bs i).Encloses (Foundation.entropyTerm (p i))) :
    (pairSumBall bs).Encloses (Foundation.finiteEntropy p) :=
  pairSumBall_sound _ _ h

lemma pairLawBall_sound_on {A : Type*} [Fintype A] (support : List Shape) (s : Shape)
    (bs : Shape → Ball) (p : Shape → ℝ) (bq : Shape → A → Ball) (q : Shape → A → ℝ)
    (hp : ∀ u ∈ support, (bs u).Encloses (p u))
    (hq : ∀ u ∈ support, ∀ a, (bq u a).Encloses (q u a))
    (hcq : ∀ u ∈ support, ∀ a, (bq (complement s u) a).Encloses (q (complement s u) a))
    (ij : A × A) :
    (pairLawBall support s bs bq ij).Encloses (pairLaw support s p q ij) := by
  apply listSumBall_sound
  intro u hu
  exact Ball.mul_sound (Ball.mul_sound (hp u hu) (hq u hu ij.1)) (hcq u hu ij.2)

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

lemma singletonBall_sound {A : Type*} [Fintype A] (support : List Shape)
    (bs : Shape → Ball) (p : Shape → ℝ) (priority : Placement) (position : Fin 3)
    (be : Shape → Ball) (q : Shape → A → ℝ)
    (hp : ∀ u ∈ support, (bs u).Encloses (p u))
    (he : ∀ u ∈ support, designated priority position u →
      (be u).Encloses (homogeneousEntropy (q u))) :
    (singletonBall support bs priority position be).Encloses
      (singletonEntropy support p priority position q) := by
  apply listSumBall_sound
  intro u hu
  by_cases hk : designated priority position u
  · simpa only [hk, ite_true, if_true] using Ball.mul_sound (hp u hu) (he u hu hk)
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
lemma B5_1_2Binary_eq (u : Shape) (hu : u ∈ shapes 4) :
    binaryParameter (shape 5 1 2) u = B5_1_2Binary u := by
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

lemma B5_1_2Little_sound (u : Shape) (w : Fin 3) (i : Fin 6) :
    (B5_1_2Little u w i).Encloses (littleLaw (shape 5 1 2) u w i : ℝ) := by
  by_cases hu : u ∈ shapes 4
  · simp only [B5_1_2Little, hu, ite_true, if_true]
    apply exact_rat_enclosed
    simp only [B5_1_2LittleRat, littleLaw, B5_1_2Binary_eq u hu]
  · simp only [B5_1_2Little, hu, ite_false, if_false]
    exact Ball.exact_sound _

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB5_1_2I1
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
lemma CB5_1_2I1PairRaw_sound (a : PairSlot) :
    (CB5_1_2I1PairRaw a).Encloses (CB5_1_2I1PairValue a) := by
  exact pairLawBall_sound_on (below (shape 5 1 2)) (shape 5 1 2) B5_1_2Law (fun u => (stageBLaw (shape 5 1 2) u : ℝ)) (fun u => B5_1_2Little u ((stageBPriority (shape 5 1 2)) 1)) (fun u a => (littleLaw (shape 5 1 2) u ((stageBPriority (shape 5 1 2)) 1) a : ℝ)) (fun u _ => B5_1_2Law_sound u) (fun u _ a => B5_1_2Little_sound u ((stageBPriority (shape 5 1 2)) 1) a) (fun u _ a => B5_1_2Little_sound (complement (shape 5 1 2) u) ((stageBPriority (shape 5 1 2)) 1) a) a
lemma CB5_1_2I1PairCertificates_valid :
    CB5_1_2I1PairCertificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB5_1_2I1PairP_check : ∀ a : PairSlot, contains (CB5_1_2I1PairRaw a) (CB5_1_2I1PairP a) = true := by
  decide +kernel
lemma CB5_1_2I1PairP_sound (a : PairSlot) :
    (CB5_1_2I1PairP a).Encloses (CB5_1_2I1PairValue a) :=
  contains_sound (CB5_1_2I1PairRaw_sound a) (CB5_1_2I1PairP_check a)
lemma CB5_1_2I1PairTerms_sound (a : PairSlot) :
    (CB5_1_2I1PairTerms a).Encloses (Foundation.entropyTerm (CB5_1_2I1PairValue a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB5_1_2I1PairCertificates_valid
    (CB5_1_2I1PairCertificateIndex a) (CB5_1_2I1PairP_sound a)
lemma CB5_1_2I1PairEntropy_sound : CB5_1_2I1PairEntropy.Encloses (Foundation.finiteEntropy CB5_1_2I1PairValue) := by
  exact contains_sound (entropyPair_enclosed CB5_1_2I1PairValue CB5_1_2I1PairTerms CB5_1_2I1PairTerms_sound) (by decide +kernel)
lemma CB5_1_2I1PairMass_sound : CB5_1_2I1PairMass.Encloses (∑ a, CB5_1_2I1PairValue a) := by
  exact contains_sound (pairSumBall_sound CB5_1_2I1PairP CB5_1_2I1PairValue CB5_1_2I1PairP_sound) (by decide +kernel)
lemma CB5_1_2I1PairMassTermLog_sound : CB5_1_2I1PairMassTermLog.Encloses (Real.log ((∑ a, CB5_1_2I1PairValue a))) := by
  exact checkLog_sound logTwoBall_sound (CB5_1_2I1PairMass_sound) (w := CB5_1_2I1PairMassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CB5_1_2I1PairMassTerm_sound : CB5_1_2I1PairMassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB5_1_2I1PairValue a))) := by
  exact contains_sound (entropyTerm_ball (CB5_1_2I1PairMass_sound) CB5_1_2I1PairMassTermLog_sound) (by decide +kernel)
lemma CB5_1_2I1PairH_sound : CB5_1_2I1PairH.Encloses (homogeneousEntropy CB5_1_2I1PairValue) := by
  exact contains_sound (homogeneous_enclosed CB5_1_2I1PairValue CB5_1_2I1PairMassTerm_sound CB5_1_2I1PairEntropy_sound) (by decide +kernel)

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
lemma CB5_1_2I1R0Raw_sound (a : Fin 6) :
    (CB5_1_2I1R0Raw a).Encloses (CB5_1_2I1R0Value a) := by
  exact residualBall_sound_on (below (shape 5 1 2)) B5_1_2Law (fun u => (stageBLaw (shape 5 1 2) u : ℝ)) (stageBPriority (shape 5 1 2)) 1 (fun u => B5_1_2Little u ((stageBPriority (shape 5 1 2)) 1)) (fun u a => (littleLaw (shape 5 1 2) u ((stageBPriority (shape 5 1 2)) 1) a : ℝ)) (fun u _ => B5_1_2Law_sound u) (fun u _ a => B5_1_2Little_sound u ((stageBPriority (shape 5 1 2)) 1) a) 0 a
lemma CB5_1_2I1R0Certificates_valid :
    CB5_1_2I1R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB5_1_2I1R0P_check : ∀ a : Fin 6, contains (CB5_1_2I1R0Raw a) (CB5_1_2I1R0P a) = true := by
  decide +kernel
lemma CB5_1_2I1R0P_sound (a : Fin 6) :
    (CB5_1_2I1R0P a).Encloses (CB5_1_2I1R0Value a) :=
  contains_sound (CB5_1_2I1R0Raw_sound a) (CB5_1_2I1R0P_check a)
lemma CB5_1_2I1R0Terms_sound (a : Fin 6) :
    (CB5_1_2I1R0Terms a).Encloses (Foundation.entropyTerm (CB5_1_2I1R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB5_1_2I1R0Certificates_valid
    (CB5_1_2I1R0CertificateIndex a) (CB5_1_2I1R0P_sound a)
lemma CB5_1_2I1R0Entropy_sound : CB5_1_2I1R0Entropy.Encloses (Foundation.finiteEntropy CB5_1_2I1R0Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB5_1_2I1R0Value CB5_1_2I1R0Terms CB5_1_2I1R0Terms_sound) (by decide +kernel)
lemma CB5_1_2I1R0Mass_sound : CB5_1_2I1R0Mass.Encloses (∑ a, CB5_1_2I1R0Value a) := by
  exact contains_sound (finSumBall_sound 6 CB5_1_2I1R0P CB5_1_2I1R0Value CB5_1_2I1R0P_sound) (by decide +kernel)
lemma CB5_1_2I1R0MassTermLog_sound : CB5_1_2I1R0MassTermLog.Encloses (Real.log ((∑ a, CB5_1_2I1R0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB5_1_2I1R0Mass_sound) (w := CB5_1_2I1R0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CB5_1_2I1R0MassTerm_sound : CB5_1_2I1R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB5_1_2I1R0Value a))) := by
  exact contains_sound (entropyTerm_ball (CB5_1_2I1R0Mass_sound) CB5_1_2I1R0MassTermLog_sound) (by decide +kernel)
lemma CB5_1_2I1R0H_sound : CB5_1_2I1R0H.Encloses (homogeneousEntropy CB5_1_2I1R0Value) := by
  exact contains_sound (homogeneous_enclosed CB5_1_2I1R0Value CB5_1_2I1R0MassTerm_sound CB5_1_2I1R0Entropy_sound) (by decide +kernel)
lemma CB5_1_2I1R1Raw_sound (a : Fin 6) :
    (CB5_1_2I1R1Raw a).Encloses (CB5_1_2I1R1Value a) := by
  exact residualBall_sound_on (below (shape 5 1 2)) B5_1_2Law (fun u => (stageBLaw (shape 5 1 2) u : ℝ)) (stageBPriority (shape 5 1 2)) 1 (fun u => B5_1_2Little u ((stageBPriority (shape 5 1 2)) 1)) (fun u a => (littleLaw (shape 5 1 2) u ((stageBPriority (shape 5 1 2)) 1) a : ℝ)) (fun u _ => B5_1_2Law_sound u) (fun u _ a => B5_1_2Little_sound u ((stageBPriority (shape 5 1 2)) 1) a) 1 a
lemma CB5_1_2I1R1Certificates_valid :
    CB5_1_2I1R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB5_1_2I1R1P_check : ∀ a : Fin 6, contains (CB5_1_2I1R1Raw a) (CB5_1_2I1R1P a) = true := by
  decide +kernel
lemma CB5_1_2I1R1P_sound (a : Fin 6) :
    (CB5_1_2I1R1P a).Encloses (CB5_1_2I1R1Value a) :=
  contains_sound (CB5_1_2I1R1Raw_sound a) (CB5_1_2I1R1P_check a)
lemma CB5_1_2I1R1Terms_sound (a : Fin 6) :
    (CB5_1_2I1R1Terms a).Encloses (Foundation.entropyTerm (CB5_1_2I1R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB5_1_2I1R1Certificates_valid
    (CB5_1_2I1R1CertificateIndex a) (CB5_1_2I1R1P_sound a)
lemma CB5_1_2I1R1Entropy_sound : CB5_1_2I1R1Entropy.Encloses (Foundation.finiteEntropy CB5_1_2I1R1Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB5_1_2I1R1Value CB5_1_2I1R1Terms CB5_1_2I1R1Terms_sound) (by decide +kernel)
lemma CB5_1_2I1R1Mass_sound : CB5_1_2I1R1Mass.Encloses (∑ a, CB5_1_2I1R1Value a) := by
  exact contains_sound (finSumBall_sound 6 CB5_1_2I1R1P CB5_1_2I1R1Value CB5_1_2I1R1P_sound) (by decide +kernel)
lemma CB5_1_2I1R1MassTermLog_sound : CB5_1_2I1R1MassTermLog.Encloses (Real.log ((∑ a, CB5_1_2I1R1Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB5_1_2I1R1Mass_sound) (w := CB5_1_2I1R1MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CB5_1_2I1R1MassTerm_sound : CB5_1_2I1R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB5_1_2I1R1Value a))) := by
  exact contains_sound (entropyTerm_ball (CB5_1_2I1R1Mass_sound) CB5_1_2I1R1MassTermLog_sound) (by decide +kernel)
lemma CB5_1_2I1R1H_sound : CB5_1_2I1R1H.Encloses (homogeneousEntropy CB5_1_2I1R1Value) := by
  exact contains_sound (homogeneous_enclosed CB5_1_2I1R1Value CB5_1_2I1R1MassTerm_sound CB5_1_2I1R1Entropy_sound) (by decide +kernel)
lemma CB5_1_2I1R2Raw_sound (a : Fin 6) :
    (CB5_1_2I1R2Raw a).Encloses (CB5_1_2I1R2Value a) := by
  exact residualBall_sound_on (below (shape 5 1 2)) B5_1_2Law (fun u => (stageBLaw (shape 5 1 2) u : ℝ)) (stageBPriority (shape 5 1 2)) 1 (fun u => B5_1_2Little u ((stageBPriority (shape 5 1 2)) 1)) (fun u a => (littleLaw (shape 5 1 2) u ((stageBPriority (shape 5 1 2)) 1) a : ℝ)) (fun u _ => B5_1_2Law_sound u) (fun u _ a => B5_1_2Little_sound u ((stageBPriority (shape 5 1 2)) 1) a) 2 a
lemma CB5_1_2I1R2Certificates_valid :
    CB5_1_2I1R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB5_1_2I1R2P_check : ∀ a : Fin 6, contains (CB5_1_2I1R2Raw a) (CB5_1_2I1R2P a) = true := by
  decide +kernel
lemma CB5_1_2I1R2P_sound (a : Fin 6) :
    (CB5_1_2I1R2P a).Encloses (CB5_1_2I1R2Value a) :=
  contains_sound (CB5_1_2I1R2Raw_sound a) (CB5_1_2I1R2P_check a)
lemma CB5_1_2I1R2Terms_sound (a : Fin 6) :
    (CB5_1_2I1R2Terms a).Encloses (Foundation.entropyTerm (CB5_1_2I1R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB5_1_2I1R2Certificates_valid
    (CB5_1_2I1R2CertificateIndex a) (CB5_1_2I1R2P_sound a)
lemma CB5_1_2I1R2Entropy_sound : CB5_1_2I1R2Entropy.Encloses (Foundation.finiteEntropy CB5_1_2I1R2Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB5_1_2I1R2Value CB5_1_2I1R2Terms CB5_1_2I1R2Terms_sound) (by decide +kernel)
lemma CB5_1_2I1R2Mass_sound : CB5_1_2I1R2Mass.Encloses (∑ a, CB5_1_2I1R2Value a) := by
  exact contains_sound (finSumBall_sound 6 CB5_1_2I1R2P CB5_1_2I1R2Value CB5_1_2I1R2P_sound) (by decide +kernel)
lemma CB5_1_2I1R2MassTermLog_sound : CB5_1_2I1R2MassTermLog.Encloses (Real.log ((∑ a, CB5_1_2I1R2Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB5_1_2I1R2Mass_sound) (w := CB5_1_2I1R2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CB5_1_2I1R2MassTerm_sound : CB5_1_2I1R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB5_1_2I1R2Value a))) := by
  exact contains_sound (entropyTerm_ball (CB5_1_2I1R2Mass_sound) CB5_1_2I1R2MassTermLog_sound) (by decide +kernel)
lemma CB5_1_2I1R2H_sound : CB5_1_2I1R2H.Encloses (homogeneousEntropy CB5_1_2I1R2Value) := by
  exact contains_sound (homogeneous_enclosed CB5_1_2I1R2Value CB5_1_2I1R2MassTerm_sound CB5_1_2I1R2Entropy_sound) (by decide +kernel)
lemma CB5_1_2I1R3Raw_sound (a : Fin 6) :
    (CB5_1_2I1R3Raw a).Encloses (CB5_1_2I1R3Value a) := by
  exact residualBall_sound_on (below (shape 5 1 2)) B5_1_2Law (fun u => (stageBLaw (shape 5 1 2) u : ℝ)) (stageBPriority (shape 5 1 2)) 1 (fun u => B5_1_2Little u ((stageBPriority (shape 5 1 2)) 1)) (fun u a => (littleLaw (shape 5 1 2) u ((stageBPriority (shape 5 1 2)) 1) a : ℝ)) (fun u _ => B5_1_2Law_sound u) (fun u _ a => B5_1_2Little_sound u ((stageBPriority (shape 5 1 2)) 1) a) 3 a
lemma CB5_1_2I1R3Certificates_valid :
    CB5_1_2I1R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB5_1_2I1R3P_check : ∀ a : Fin 6, contains (CB5_1_2I1R3Raw a) (CB5_1_2I1R3P a) = true := by
  decide +kernel
lemma CB5_1_2I1R3P_sound (a : Fin 6) :
    (CB5_1_2I1R3P a).Encloses (CB5_1_2I1R3Value a) :=
  contains_sound (CB5_1_2I1R3Raw_sound a) (CB5_1_2I1R3P_check a)
lemma CB5_1_2I1R3Terms_sound (a : Fin 6) :
    (CB5_1_2I1R3Terms a).Encloses (Foundation.entropyTerm (CB5_1_2I1R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB5_1_2I1R3Certificates_valid
    (CB5_1_2I1R3CertificateIndex a) (CB5_1_2I1R3P_sound a)
lemma CB5_1_2I1R3Entropy_sound : CB5_1_2I1R3Entropy.Encloses (Foundation.finiteEntropy CB5_1_2I1R3Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB5_1_2I1R3Value CB5_1_2I1R3Terms CB5_1_2I1R3Terms_sound) (by decide +kernel)
lemma CB5_1_2I1R3Mass_sound : CB5_1_2I1R3Mass.Encloses (∑ a, CB5_1_2I1R3Value a) := by
  exact contains_sound (finSumBall_sound 6 CB5_1_2I1R3P CB5_1_2I1R3Value CB5_1_2I1R3P_sound) (by decide +kernel)
lemma CB5_1_2I1R3MassTerm_sound : CB5_1_2I1R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB5_1_2I1R3Value a))) :=
  entropyTerm_zero_ball (CB5_1_2I1R3Mass_sound)
lemma CB5_1_2I1R3H_sound : CB5_1_2I1R3H.Encloses (homogeneousEntropy CB5_1_2I1R3Value) := by
  exact contains_sound (homogeneous_enclosed CB5_1_2I1R3Value CB5_1_2I1R3MassTerm_sound CB5_1_2I1R3Entropy_sound) (by decide +kernel)
lemma CB5_1_2I1R4Raw_sound (a : Fin 6) :
    (CB5_1_2I1R4Raw a).Encloses (CB5_1_2I1R4Value a) := by
  exact residualBall_sound_on (below (shape 5 1 2)) B5_1_2Law (fun u => (stageBLaw (shape 5 1 2) u : ℝ)) (stageBPriority (shape 5 1 2)) 1 (fun u => B5_1_2Little u ((stageBPriority (shape 5 1 2)) 1)) (fun u a => (littleLaw (shape 5 1 2) u ((stageBPriority (shape 5 1 2)) 1) a : ℝ)) (fun u _ => B5_1_2Law_sound u) (fun u _ a => B5_1_2Little_sound u ((stageBPriority (shape 5 1 2)) 1) a) 4 a
lemma CB5_1_2I1R4Certificates_valid :
    CB5_1_2I1R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB5_1_2I1R4P_check : ∀ a : Fin 6, contains (CB5_1_2I1R4Raw a) (CB5_1_2I1R4P a) = true := by
  decide +kernel
lemma CB5_1_2I1R4P_sound (a : Fin 6) :
    (CB5_1_2I1R4P a).Encloses (CB5_1_2I1R4Value a) :=
  contains_sound (CB5_1_2I1R4Raw_sound a) (CB5_1_2I1R4P_check a)
lemma CB5_1_2I1R4Terms_sound (a : Fin 6) :
    (CB5_1_2I1R4Terms a).Encloses (Foundation.entropyTerm (CB5_1_2I1R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB5_1_2I1R4Certificates_valid
    (CB5_1_2I1R4CertificateIndex a) (CB5_1_2I1R4P_sound a)
lemma CB5_1_2I1R4Entropy_sound : CB5_1_2I1R4Entropy.Encloses (Foundation.finiteEntropy CB5_1_2I1R4Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB5_1_2I1R4Value CB5_1_2I1R4Terms CB5_1_2I1R4Terms_sound) (by decide +kernel)
lemma CB5_1_2I1R4Mass_sound : CB5_1_2I1R4Mass.Encloses (∑ a, CB5_1_2I1R4Value a) := by
  exact contains_sound (finSumBall_sound 6 CB5_1_2I1R4P CB5_1_2I1R4Value CB5_1_2I1R4P_sound) (by decide +kernel)
lemma CB5_1_2I1R4MassTerm_sound : CB5_1_2I1R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB5_1_2I1R4Value a))) :=
  entropyTerm_zero_ball (CB5_1_2I1R4Mass_sound)
lemma CB5_1_2I1R4H_sound : CB5_1_2I1R4H.Encloses (homogeneousEntropy CB5_1_2I1R4Value) := by
  exact contains_sound (homogeneous_enclosed CB5_1_2I1R4Value CB5_1_2I1R4MassTerm_sound CB5_1_2I1R4Entropy_sound) (by decide +kernel)
lemma CB5_1_2I1R5Raw_sound (a : Fin 6) :
    (CB5_1_2I1R5Raw a).Encloses (CB5_1_2I1R5Value a) := by
  exact residualBall_sound_on (below (shape 5 1 2)) B5_1_2Law (fun u => (stageBLaw (shape 5 1 2) u : ℝ)) (stageBPriority (shape 5 1 2)) 1 (fun u => B5_1_2Little u ((stageBPriority (shape 5 1 2)) 1)) (fun u a => (littleLaw (shape 5 1 2) u ((stageBPriority (shape 5 1 2)) 1) a : ℝ)) (fun u _ => B5_1_2Law_sound u) (fun u _ a => B5_1_2Little_sound u ((stageBPriority (shape 5 1 2)) 1) a) 5 a
lemma CB5_1_2I1R5Certificates_valid :
    CB5_1_2I1R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB5_1_2I1R5P_check : ∀ a : Fin 6, contains (CB5_1_2I1R5Raw a) (CB5_1_2I1R5P a) = true := by
  decide +kernel
lemma CB5_1_2I1R5P_sound (a : Fin 6) :
    (CB5_1_2I1R5P a).Encloses (CB5_1_2I1R5Value a) :=
  contains_sound (CB5_1_2I1R5Raw_sound a) (CB5_1_2I1R5P_check a)
lemma CB5_1_2I1R5Terms_sound (a : Fin 6) :
    (CB5_1_2I1R5Terms a).Encloses (Foundation.entropyTerm (CB5_1_2I1R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB5_1_2I1R5Certificates_valid
    (CB5_1_2I1R5CertificateIndex a) (CB5_1_2I1R5P_sound a)
lemma CB5_1_2I1R5Entropy_sound : CB5_1_2I1R5Entropy.Encloses (Foundation.finiteEntropy CB5_1_2I1R5Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB5_1_2I1R5Value CB5_1_2I1R5Terms CB5_1_2I1R5Terms_sound) (by decide +kernel)
lemma CB5_1_2I1R5Mass_sound : CB5_1_2I1R5Mass.Encloses (∑ a, CB5_1_2I1R5Value a) := by
  exact contains_sound (finSumBall_sound 6 CB5_1_2I1R5P CB5_1_2I1R5Value CB5_1_2I1R5P_sound) (by decide +kernel)
lemma CB5_1_2I1R5MassTerm_sound : CB5_1_2I1R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB5_1_2I1R5Value a))) :=
  entropyTerm_zero_ball (CB5_1_2I1R5Mass_sound)
lemma CB5_1_2I1R5H_sound : CB5_1_2I1R5H.Encloses (homogeneousEntropy CB5_1_2I1R5Value) := by
  exact contains_sound (homogeneous_enclosed CB5_1_2I1R5Value CB5_1_2I1R5MassTerm_sound CB5_1_2I1R5Entropy_sound) (by decide +kernel)
lemma CB5_1_2I1R6Raw_sound (a : Fin 6) :
    (CB5_1_2I1R6Raw a).Encloses (CB5_1_2I1R6Value a) := by
  exact residualBall_sound_on (below (shape 5 1 2)) B5_1_2Law (fun u => (stageBLaw (shape 5 1 2) u : ℝ)) (stageBPriority (shape 5 1 2)) 1 (fun u => B5_1_2Little u ((stageBPriority (shape 5 1 2)) 1)) (fun u a => (littleLaw (shape 5 1 2) u ((stageBPriority (shape 5 1 2)) 1) a : ℝ)) (fun u _ => B5_1_2Law_sound u) (fun u _ a => B5_1_2Little_sound u ((stageBPriority (shape 5 1 2)) 1) a) 6 a
lemma CB5_1_2I1R6Certificates_valid :
    CB5_1_2I1R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB5_1_2I1R6P_check : ∀ a : Fin 6, contains (CB5_1_2I1R6Raw a) (CB5_1_2I1R6P a) = true := by
  decide +kernel
lemma CB5_1_2I1R6P_sound (a : Fin 6) :
    (CB5_1_2I1R6P a).Encloses (CB5_1_2I1R6Value a) :=
  contains_sound (CB5_1_2I1R6Raw_sound a) (CB5_1_2I1R6P_check a)
lemma CB5_1_2I1R6Terms_sound (a : Fin 6) :
    (CB5_1_2I1R6Terms a).Encloses (Foundation.entropyTerm (CB5_1_2I1R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB5_1_2I1R6Certificates_valid
    (CB5_1_2I1R6CertificateIndex a) (CB5_1_2I1R6P_sound a)
lemma CB5_1_2I1R6Entropy_sound : CB5_1_2I1R6Entropy.Encloses (Foundation.finiteEntropy CB5_1_2I1R6Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB5_1_2I1R6Value CB5_1_2I1R6Terms CB5_1_2I1R6Terms_sound) (by decide +kernel)
lemma CB5_1_2I1R6Mass_sound : CB5_1_2I1R6Mass.Encloses (∑ a, CB5_1_2I1R6Value a) := by
  exact contains_sound (finSumBall_sound 6 CB5_1_2I1R6P CB5_1_2I1R6Value CB5_1_2I1R6P_sound) (by decide +kernel)
lemma CB5_1_2I1R6MassTerm_sound : CB5_1_2I1R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB5_1_2I1R6Value a))) :=
  entropyTerm_zero_ball (CB5_1_2I1R6Mass_sound)
lemma CB5_1_2I1R6H_sound : CB5_1_2I1R6H.Encloses (homogeneousEntropy CB5_1_2I1R6Value) := by
  exact contains_sound (homogeneous_enclosed CB5_1_2I1R6Value CB5_1_2I1R6MassTerm_sound CB5_1_2I1R6Entropy_sound) (by decide +kernel)
lemma CB5_1_2I1R7Raw_sound (a : Fin 6) :
    (CB5_1_2I1R7Raw a).Encloses (CB5_1_2I1R7Value a) := by
  exact residualBall_sound_on (below (shape 5 1 2)) B5_1_2Law (fun u => (stageBLaw (shape 5 1 2) u : ℝ)) (stageBPriority (shape 5 1 2)) 1 (fun u => B5_1_2Little u ((stageBPriority (shape 5 1 2)) 1)) (fun u a => (littleLaw (shape 5 1 2) u ((stageBPriority (shape 5 1 2)) 1) a : ℝ)) (fun u _ => B5_1_2Law_sound u) (fun u _ a => B5_1_2Little_sound u ((stageBPriority (shape 5 1 2)) 1) a) 7 a
lemma CB5_1_2I1R7Certificates_valid :
    CB5_1_2I1R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB5_1_2I1R7P_check : ∀ a : Fin 6, contains (CB5_1_2I1R7Raw a) (CB5_1_2I1R7P a) = true := by
  decide +kernel
lemma CB5_1_2I1R7P_sound (a : Fin 6) :
    (CB5_1_2I1R7P a).Encloses (CB5_1_2I1R7Value a) :=
  contains_sound (CB5_1_2I1R7Raw_sound a) (CB5_1_2I1R7P_check a)
lemma CB5_1_2I1R7Terms_sound (a : Fin 6) :
    (CB5_1_2I1R7Terms a).Encloses (Foundation.entropyTerm (CB5_1_2I1R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB5_1_2I1R7Certificates_valid
    (CB5_1_2I1R7CertificateIndex a) (CB5_1_2I1R7P_sound a)
lemma CB5_1_2I1R7Entropy_sound : CB5_1_2I1R7Entropy.Encloses (Foundation.finiteEntropy CB5_1_2I1R7Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB5_1_2I1R7Value CB5_1_2I1R7Terms CB5_1_2I1R7Terms_sound) (by decide +kernel)
lemma CB5_1_2I1R7Mass_sound : CB5_1_2I1R7Mass.Encloses (∑ a, CB5_1_2I1R7Value a) := by
  exact contains_sound (finSumBall_sound 6 CB5_1_2I1R7P CB5_1_2I1R7Value CB5_1_2I1R7P_sound) (by decide +kernel)
lemma CB5_1_2I1R7MassTerm_sound : CB5_1_2I1R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB5_1_2I1R7Value a))) :=
  entropyTerm_zero_ball (CB5_1_2I1R7Mass_sound)
lemma CB5_1_2I1R7H_sound : CB5_1_2I1R7H.Encloses (homogeneousEntropy CB5_1_2I1R7Value) := by
  exact contains_sound (homogeneous_enclosed CB5_1_2I1R7Value CB5_1_2I1R7MassTerm_sound CB5_1_2I1R7Entropy_sound) (by decide +kernel)
lemma CB5_1_2I1R8Raw_sound (a : Fin 6) :
    (CB5_1_2I1R8Raw a).Encloses (CB5_1_2I1R8Value a) := by
  exact residualBall_sound_on (below (shape 5 1 2)) B5_1_2Law (fun u => (stageBLaw (shape 5 1 2) u : ℝ)) (stageBPriority (shape 5 1 2)) 1 (fun u => B5_1_2Little u ((stageBPriority (shape 5 1 2)) 1)) (fun u a => (littleLaw (shape 5 1 2) u ((stageBPriority (shape 5 1 2)) 1) a : ℝ)) (fun u _ => B5_1_2Law_sound u) (fun u _ a => B5_1_2Little_sound u ((stageBPriority (shape 5 1 2)) 1) a) 8 a
lemma CB5_1_2I1R8Certificates_valid :
    CB5_1_2I1R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB5_1_2I1R8P_check : ∀ a : Fin 6, contains (CB5_1_2I1R8Raw a) (CB5_1_2I1R8P a) = true := by
  decide +kernel
lemma CB5_1_2I1R8P_sound (a : Fin 6) :
    (CB5_1_2I1R8P a).Encloses (CB5_1_2I1R8Value a) :=
  contains_sound (CB5_1_2I1R8Raw_sound a) (CB5_1_2I1R8P_check a)
lemma CB5_1_2I1R8Terms_sound (a : Fin 6) :
    (CB5_1_2I1R8Terms a).Encloses (Foundation.entropyTerm (CB5_1_2I1R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB5_1_2I1R8Certificates_valid
    (CB5_1_2I1R8CertificateIndex a) (CB5_1_2I1R8P_sound a)
lemma CB5_1_2I1R8Entropy_sound : CB5_1_2I1R8Entropy.Encloses (Foundation.finiteEntropy CB5_1_2I1R8Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB5_1_2I1R8Value CB5_1_2I1R8Terms CB5_1_2I1R8Terms_sound) (by decide +kernel)
lemma CB5_1_2I1R8Mass_sound : CB5_1_2I1R8Mass.Encloses (∑ a, CB5_1_2I1R8Value a) := by
  exact contains_sound (finSumBall_sound 6 CB5_1_2I1R8P CB5_1_2I1R8Value CB5_1_2I1R8P_sound) (by decide +kernel)
lemma CB5_1_2I1R8MassTerm_sound : CB5_1_2I1R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB5_1_2I1R8Value a))) :=
  entropyTerm_zero_ball (CB5_1_2I1R8Mass_sound)
lemma CB5_1_2I1R8H_sound : CB5_1_2I1R8H.Encloses (homogeneousEntropy CB5_1_2I1R8Value) := by
  exact contains_sound (homogeneous_enclosed CB5_1_2I1R8Value CB5_1_2I1R8MassTerm_sound CB5_1_2I1R8Entropy_sound) (by decide +kernel)
lemma CB5_1_2I1R9Raw_sound (a : Fin 6) :
    (CB5_1_2I1R9Raw a).Encloses (CB5_1_2I1R9Value a) := by
  exact residualBall_sound_on (below (shape 5 1 2)) B5_1_2Law (fun u => (stageBLaw (shape 5 1 2) u : ℝ)) (stageBPriority (shape 5 1 2)) 1 (fun u => B5_1_2Little u ((stageBPriority (shape 5 1 2)) 1)) (fun u a => (littleLaw (shape 5 1 2) u ((stageBPriority (shape 5 1 2)) 1) a : ℝ)) (fun u _ => B5_1_2Law_sound u) (fun u _ a => B5_1_2Little_sound u ((stageBPriority (shape 5 1 2)) 1) a) 9 a
lemma CB5_1_2I1R9Certificates_valid :
    CB5_1_2I1R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB5_1_2I1R9P_check : ∀ a : Fin 6, contains (CB5_1_2I1R9Raw a) (CB5_1_2I1R9P a) = true := by
  decide +kernel
lemma CB5_1_2I1R9P_sound (a : Fin 6) :
    (CB5_1_2I1R9P a).Encloses (CB5_1_2I1R9Value a) :=
  contains_sound (CB5_1_2I1R9Raw_sound a) (CB5_1_2I1R9P_check a)
lemma CB5_1_2I1R9Terms_sound (a : Fin 6) :
    (CB5_1_2I1R9Terms a).Encloses (Foundation.entropyTerm (CB5_1_2I1R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB5_1_2I1R9Certificates_valid
    (CB5_1_2I1R9CertificateIndex a) (CB5_1_2I1R9P_sound a)
lemma CB5_1_2I1R9Entropy_sound : CB5_1_2I1R9Entropy.Encloses (Foundation.finiteEntropy CB5_1_2I1R9Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB5_1_2I1R9Value CB5_1_2I1R9Terms CB5_1_2I1R9Terms_sound) (by decide +kernel)
lemma CB5_1_2I1R9Mass_sound : CB5_1_2I1R9Mass.Encloses (∑ a, CB5_1_2I1R9Value a) := by
  exact contains_sound (finSumBall_sound 6 CB5_1_2I1R9P CB5_1_2I1R9Value CB5_1_2I1R9P_sound) (by decide +kernel)
lemma CB5_1_2I1R9MassTerm_sound : CB5_1_2I1R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB5_1_2I1R9Value a))) :=
  entropyTerm_zero_ball (CB5_1_2I1R9Mass_sound)
lemma CB5_1_2I1R9H_sound : CB5_1_2I1R9H.Encloses (homogeneousEntropy CB5_1_2I1R9Value) := by
  exact contains_sound (homogeneous_enclosed CB5_1_2I1R9Value CB5_1_2I1R9MassTerm_sound CB5_1_2I1R9Entropy_sound) (by decide +kernel)
lemma CB5_1_2I1R15Raw_sound (a : Fin 6) :
    (CB5_1_2I1R15Raw a).Encloses (CB5_1_2I1R15Value a) := by
  exact residualBall_sound_on (below (shape 5 1 2)) B5_1_2Law (fun u => (stageBLaw (shape 5 1 2) u : ℝ)) (stageBPriority (shape 5 1 2)) 1 (fun u => B5_1_2Little u ((stageBPriority (shape 5 1 2)) 1)) (fun u a => (littleLaw (shape 5 1 2) u ((stageBPriority (shape 5 1 2)) 1) a : ℝ)) (fun u _ => B5_1_2Law_sound u) (fun u _ a => B5_1_2Little_sound u ((stageBPriority (shape 5 1 2)) 1) a) 15 a
lemma CB5_1_2I1R15Certificates_valid :
    CB5_1_2I1R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB5_1_2I1R15P_check : ∀ a : Fin 6, contains (CB5_1_2I1R15Raw a) (CB5_1_2I1R15P a) = true := by
  decide +kernel
lemma CB5_1_2I1R15P_sound (a : Fin 6) :
    (CB5_1_2I1R15P a).Encloses (CB5_1_2I1R15Value a) :=
  contains_sound (CB5_1_2I1R15Raw_sound a) (CB5_1_2I1R15P_check a)
lemma CB5_1_2I1R15Terms_sound (a : Fin 6) :
    (CB5_1_2I1R15Terms a).Encloses (Foundation.entropyTerm (CB5_1_2I1R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB5_1_2I1R15Certificates_valid
    (CB5_1_2I1R15CertificateIndex a) (CB5_1_2I1R15P_sound a)
lemma CB5_1_2I1R15Entropy_sound : CB5_1_2I1R15Entropy.Encloses (Foundation.finiteEntropy CB5_1_2I1R15Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB5_1_2I1R15Value CB5_1_2I1R15Terms CB5_1_2I1R15Terms_sound) (by decide +kernel)
lemma CB5_1_2I1R15Mass_sound : CB5_1_2I1R15Mass.Encloses (∑ a, CB5_1_2I1R15Value a) := by
  exact contains_sound (finSumBall_sound 6 CB5_1_2I1R15P CB5_1_2I1R15Value CB5_1_2I1R15P_sound) (by decide +kernel)
lemma CB5_1_2I1R15MassTerm_sound : CB5_1_2I1R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB5_1_2I1R15Value a))) :=
  entropyTerm_zero_ball (CB5_1_2I1R15Mass_sound)
lemma CB5_1_2I1R15H_sound : CB5_1_2I1R15H.Encloses (homogeneousEntropy CB5_1_2I1R15Value) := by
  exact contains_sound (homogeneous_enclosed CB5_1_2I1R15Value CB5_1_2I1R15MassTerm_sound CB5_1_2I1R15Entropy_sound) (by decide +kernel)
lemma CB5_1_2I1R16Raw_sound (a : Fin 6) :
    (CB5_1_2I1R16Raw a).Encloses (CB5_1_2I1R16Value a) := by
  exact residualBall_sound_on (below (shape 5 1 2)) B5_1_2Law (fun u => (stageBLaw (shape 5 1 2) u : ℝ)) (stageBPriority (shape 5 1 2)) 1 (fun u => B5_1_2Little u ((stageBPriority (shape 5 1 2)) 1)) (fun u a => (littleLaw (shape 5 1 2) u ((stageBPriority (shape 5 1 2)) 1) a : ℝ)) (fun u _ => B5_1_2Law_sound u) (fun u _ a => B5_1_2Little_sound u ((stageBPriority (shape 5 1 2)) 1) a) 16 a
lemma CB5_1_2I1R16Certificates_valid :
    CB5_1_2I1R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB5_1_2I1R16P_check : ∀ a : Fin 6, contains (CB5_1_2I1R16Raw a) (CB5_1_2I1R16P a) = true := by
  decide +kernel
lemma CB5_1_2I1R16P_sound (a : Fin 6) :
    (CB5_1_2I1R16P a).Encloses (CB5_1_2I1R16Value a) :=
  contains_sound (CB5_1_2I1R16Raw_sound a) (CB5_1_2I1R16P_check a)
lemma CB5_1_2I1R16Terms_sound (a : Fin 6) :
    (CB5_1_2I1R16Terms a).Encloses (Foundation.entropyTerm (CB5_1_2I1R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB5_1_2I1R16Certificates_valid
    (CB5_1_2I1R16CertificateIndex a) (CB5_1_2I1R16P_sound a)
lemma CB5_1_2I1R16Entropy_sound : CB5_1_2I1R16Entropy.Encloses (Foundation.finiteEntropy CB5_1_2I1R16Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB5_1_2I1R16Value CB5_1_2I1R16Terms CB5_1_2I1R16Terms_sound) (by decide +kernel)
lemma CB5_1_2I1R16Mass_sound : CB5_1_2I1R16Mass.Encloses (∑ a, CB5_1_2I1R16Value a) := by
  exact contains_sound (finSumBall_sound 6 CB5_1_2I1R16P CB5_1_2I1R16Value CB5_1_2I1R16P_sound) (by decide +kernel)
lemma CB5_1_2I1R16MassTerm_sound : CB5_1_2I1R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB5_1_2I1R16Value a))) :=
  entropyTerm_zero_ball (CB5_1_2I1R16Mass_sound)
lemma CB5_1_2I1R16H_sound : CB5_1_2I1R16H.Encloses (homogeneousEntropy CB5_1_2I1R16Value) := by
  exact contains_sound (homogeneous_enclosed CB5_1_2I1R16Value CB5_1_2I1R16MassTerm_sound CB5_1_2I1R16Entropy_sound) (by decide +kernel)
lemma CB5_1_2I1ResidualEntropies_sound (k : Fin 17) :
    (CB5_1_2I1ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 5 1 2)) (fun u => (stageBLaw (shape 5 1 2) u : ℝ)) (stageBPriority (shape 5 1 2)) 1 (fun u a => (littleLaw (shape 5 1 2) u ((stageBPriority (shape 5 1 2)) 1) a : ℝ)) k)) := by
  fin_cases k
  · exact CB5_1_2I1R0H_sound
  · exact CB5_1_2I1R1H_sound
  · exact CB5_1_2I1R2H_sound
  · exact CB5_1_2I1R3H_sound
  · exact CB5_1_2I1R4H_sound
  · exact CB5_1_2I1R5H_sound
  · exact CB5_1_2I1R6H_sound
  · exact CB5_1_2I1R7H_sound
  · exact CB5_1_2I1R8H_sound
  · exact CB5_1_2I1R9H_sound
  · exact CB5_1_2I1R10H_sound
  · exact CB5_1_2I1R11H_sound
  · exact CB5_1_2I1R12H_sound
  · exact CB5_1_2I1R13H_sound
  · exact CB5_1_2I1R14H_sound
  · exact CB5_1_2I1R15H_sound
  · exact CB5_1_2I1R16H_sound
lemma CB5_1_2I1Singles_sound (u : Shape) (hu : u ∈ below (shape 5 1 2))
    (hd : designated (stageBPriority (shape 5 1 2)) 1 u) :
    (CB5_1_2I1Singles u).Encloses (homogeneousEntropy ((fun u a => (littleLaw (shape 5 1 2) u ((stageBPriority (shape 5 1 2)) 1) a : ℝ)) u)) := by
  rw [B5_1_2_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (show ¬ designated (stageBPriority (shape 5 1 2)) 1 (shape 1 1 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (stageBPriority (shape 5 1 2)) 1 (shape 2 0 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (stageBPriority (shape 5 1 2)) 1 (shape 2 1 1) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (stageBPriority (shape 5 1 2)) 1 (shape 3 0 1) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (stageBPriority (shape 5 1 2)) 1 (shape 3 1 0) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (stageBPriority (shape 5 1 2)) 1 (shape 4 0 0) by decide +kernel) hd |>.elim
lemma CB5_1_2I1Singleton_sound : CB5_1_2I1Singleton.Encloses
    (singletonEntropy (below (shape 5 1 2)) (fun u => (stageBLaw (shape 5 1 2) u : ℝ)) (stageBPriority (shape 5 1 2)) 1 (fun u a => (littleLaw (shape 5 1 2) u ((stageBPriority (shape 5 1 2)) 1) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 5 1 2)) B5_1_2Law (fun u => (stageBLaw (shape 5 1 2) u : ℝ)) (stageBPriority (shape 5 1 2)) 1
    CB5_1_2I1Singles (fun u a => (littleLaw (shape 5 1 2) u ((stageBPriority (shape 5 1 2)) 1) a : ℝ)) (fun u _ => B5_1_2Law_sound u) CB5_1_2I1Singles_sound) (by decide +kernel)
lemma CB5_1_2I1Group_sound : CB5_1_2I1Group.Encloses
    (groupedEntropy (below (shape 5 1 2)) (fun u => (stageBLaw (shape 5 1 2) u : ℝ)) (stageBPriority (shape 5 1 2)) 1 (fun u a => (littleLaw (shape 5 1 2) u ((stageBPriority (shape 5 1 2)) 1) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CB5_1_2I1Singleton_sound
    (finSumBall_sound 17 CB5_1_2I1ResidualEntropies _ CB5_1_2I1ResidualEntropies_sound)) (by decide +kernel)

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
lemma CB5_1_2I1_sound_oai : CB5_1_2I1H.Encloses (stageBCapacity (shape 5 1 2) 1) := by
  have hb := contains_sound (Ball.add_sound CB5_1_2I1PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CB5_1_2I1Group_sound)))
    (show contains (.add CB5_1_2I1PairH (.neg (.mul (.exact 2) CB5_1_2I1Group))) CB5_1_2I1H = true by decide +kernel)
  unfold CB5_1_2I1PairValue at hb
  simpa only [stageBCapacity, nativeCapacity,
    show (1 : Fin 3) ≠ 0 by decide, ite_false, if_false, sub_eq_add_neg] using hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB5_1_2I1_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB5_1_2I1_sound_oai
