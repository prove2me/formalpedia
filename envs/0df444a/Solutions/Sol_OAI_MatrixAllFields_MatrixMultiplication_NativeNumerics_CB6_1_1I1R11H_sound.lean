-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB6_1_1I1R11H_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:20:15.642368+00:00
-- url     : https://prove2.me/submissions/44cb779b-a8c3-4048-b8e6-e4478c36d1c3

import Mathlib
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

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB6_1_1I1
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
lemma CB6_1_1I1R11Raw_sound (a : Fin 6) :
    (CB6_1_1I1R11Raw a).Encloses (CB6_1_1I1R11Value a) := by
  exact residualBall_sound_on (below (shape 6 1 1)) B6_1_1Law (fun u => (stageBLaw (shape 6 1 1) u : ℝ)) (stageBPriority (shape 6 1 1)) 1 (fun u => B6_1_1Little u ((stageBPriority (shape 6 1 1)) 1)) (fun u a => (littleLaw (shape 6 1 1) u ((stageBPriority (shape 6 1 1)) 1) a : ℝ)) (fun u _ => B6_1_1Law_sound u) (fun u _ a => B6_1_1Little_sound u ((stageBPriority (shape 6 1 1)) 1) a) 11 a
lemma CB6_1_1I1R11Certificates_valid :
    CB6_1_1I1R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB6_1_1I1R11P_check : ∀ a : Fin 6, contains (CB6_1_1I1R11Raw a) (CB6_1_1I1R11P a) = true := by
  decide +kernel
lemma CB6_1_1I1R11P_sound (a : Fin 6) :
    (CB6_1_1I1R11P a).Encloses (CB6_1_1I1R11Value a) :=
  contains_sound (CB6_1_1I1R11Raw_sound a) (CB6_1_1I1R11P_check a)
lemma CB6_1_1I1R11Terms_sound (a : Fin 6) :
    (CB6_1_1I1R11Terms a).Encloses (Foundation.entropyTerm (CB6_1_1I1R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB6_1_1I1R11Certificates_valid
    (CB6_1_1I1R11CertificateIndex a) (CB6_1_1I1R11P_sound a)
lemma CB6_1_1I1R11Entropy_sound : CB6_1_1I1R11Entropy.Encloses (Foundation.finiteEntropy CB6_1_1I1R11Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB6_1_1I1R11Value CB6_1_1I1R11Terms CB6_1_1I1R11Terms_sound) (by decide +kernel)
lemma CB6_1_1I1R11Mass_sound : CB6_1_1I1R11Mass.Encloses (∑ a, CB6_1_1I1R11Value a) := by
  exact contains_sound (finSumBall_sound 6 CB6_1_1I1R11P CB6_1_1I1R11Value CB6_1_1I1R11P_sound) (by decide +kernel)
lemma CB6_1_1I1R11MassTerm_sound : CB6_1_1I1R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB6_1_1I1R11Value a))) :=
  entropyTerm_zero_ball (CB6_1_1I1R11Mass_sound)
lemma CB6_1_1I1R11H_sound_oai : CB6_1_1I1R11H.Encloses (homogeneousEntropy CB6_1_1I1R11Value) := by
  exact contains_sound (homogeneous_enclosed CB6_1_1I1R11Value CB6_1_1I1R11MassTerm_sound CB6_1_1I1R11Entropy_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB6_1_1I1R11H_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB6_1_1I1R11H_sound_oai
