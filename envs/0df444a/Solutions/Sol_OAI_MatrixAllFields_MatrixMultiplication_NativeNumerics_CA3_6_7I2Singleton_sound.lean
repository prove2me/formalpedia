-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_6_7I2Singleton_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T14:55:57.789483+00:00
-- url     : https://prove2.me/submissions/445b5834-7e89-48d1-8003-0616a50cd6d6

import Mathlib
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
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_A3_6_7Law_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_Z0_1_7H2H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_Z0_2_6H2H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_Z0_3_5H2H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_Z0_4_4H2MassTerm_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_Z0_4_4H2Terms_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_Z0_5_3H2H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_Z0_6_2H2Entropy_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_Z0_6_2Probs_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_Z1_0_7H2H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_Z2_0_6H2Entropy_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_Z2_0_6Probs_sound
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

end Ball

end MatrixMultiplication.AllFieldCertificates

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SparseContraction
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

lemma forall_fin6 {P : Fin 6 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2)
    (h3 : P 3) (h4 : P 4) (h5 : P 5) : ∀ i, P i := by
  intro i
  fin_cases i <;> assumption

lemma pairSumBall_sound (bs : PairSlot → Ball) (v : PairSlot → ℝ)
    (h : ∀ a, (bs a).Encloses (v a)) :
    (pairSumBall bs).Encloses (∑ a, v a) := by
  exact product_fin6_enclosed _ _ (fun i j => h (i,j))

lemma entropyPair_enclosed (p : PairSlot → ℝ) (bs : PairSlot → Ball)
    (h : ∀ i, (bs i).Encloses (Foundation.entropyTerm (p i))) :
    (pairSumBall bs).Encloses (Foundation.finiteEntropy p) :=
  pairSumBall_sound _ _ h

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
lemma w189_sound : w189.Encloses (weight (-2174) : ℝ) := by
  exact weight_enclosed_of_trace (-2174) w189Trace w189S0 w189S1 w189S2 w189S3 w189S4 w189S5
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
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Four0_3_5
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
lemma w202_sound : w202.Encloses (weight (21564) : ℝ) := by
  exact weight_enclosed_of_trace (21564) w202Trace w202S0 w202S1 w202S2 w202S3 w202S4 w202S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Four0_4_4
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
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
lemma Z0_4_4H2Entropy_sound : Z0_4_4H2Entropy.Encloses (Foundation.finiteEntropy Z0_4_4H2Value) := by
  exact contains_sound (entropyPair_enclosed Z0_4_4H2Value Z0_4_4H2Terms Z0_4_4H2Terms_sound) (by decide +kernel)
lemma Z0_4_4H2H_sound : Z0_4_4H2H.Encloses (homogeneousEntropy Z0_4_4H2Value) := by
  exact contains_sound (homogeneous_enclosed Z0_4_4H2Value Z0_4_4H2MassTerm_sound Z0_4_4H2Entropy_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitB1_1_6
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
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
lemma Z0_6_2Half_sound (w : Fin 3) (ij : PairSlot) :
    (Z0_6_2Half w ij).Encloses (halfLaw (shape 0 6 2) w ij : ℝ) := by
  have hp : positive (shape 0 6 2) = false := by decide +kernel
  simp only [Z0_6_2Half, halfLaw, hp, Bool.false_eq_true, ite_false, if_false]
  split_ifs
  · exact Ball.exact_sound 1
  · exact Ball.exact_sound 0
  · exact Z0_6_2Probs_sound _
  · exact Z0_6_2Probs_sound _

lemma Z0_6_2H2Mass_sound : Z0_6_2H2Mass.Encloses (∑ a, Z0_6_2H2Value a) := by
  exact contains_sound (pairSumBall_sound (Z0_6_2Half 2) Z0_6_2H2Value (Z0_6_2Half_sound 2)) (by decide +kernel)
lemma Z0_6_2H2MassTermLog_sound : Z0_6_2H2MassTermLog.Encloses (Real.log ((∑ a, Z0_6_2H2Value a))) := by
  exact checkLog_sound logTwoBall_sound (Z0_6_2H2Mass_sound) (w := Z0_6_2H2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z0_6_2H2MassTerm_sound : Z0_6_2H2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, Z0_6_2H2Value a))) := by
  exact contains_sound (entropyTerm_ball (Z0_6_2H2Mass_sound) Z0_6_2H2MassTermLog_sound) (by decide +kernel)
lemma Z0_6_2H2H_sound : Z0_6_2H2H.Encloses (homogeneousEntropy Z0_6_2H2Value) := by
  exact contains_sound (homogeneous_enclosed Z0_6_2H2Value Z0_6_2H2MassTerm_sound Z0_6_2H2Entropy_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Four2_0_6
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
lemma Z2_0_6Half_sound (w : Fin 3) (ij : PairSlot) :
    (Z2_0_6Half w ij).Encloses (halfLaw (shape 2 0 6) w ij : ℝ) := by
  have hp : positive (shape 2 0 6) = false := by decide +kernel
  simp only [Z2_0_6Half, halfLaw, hp, Bool.false_eq_true, ite_false, if_false]
  split_ifs
  · exact Ball.exact_sound 1
  · exact Ball.exact_sound 0
  · exact Z2_0_6Probs_sound _
  · exact Z2_0_6Probs_sound _

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
lemma Z2_0_6H2Mass_sound : Z2_0_6H2Mass.Encloses (∑ a, Z2_0_6H2Value a) := by
  exact contains_sound (pairSumBall_sound (Z2_0_6Half 2) Z2_0_6H2Value (Z2_0_6Half_sound 2)) (by decide +kernel)
lemma Z2_0_6H2MassTermLog_sound : Z2_0_6H2MassTermLog.Encloses (Real.log ((∑ a, Z2_0_6H2Value a))) := by
  exact checkLog_sound logTwoBall_sound (Z2_0_6H2Mass_sound) (w := Z2_0_6H2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z2_0_6H2MassTerm_sound : Z2_0_6H2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, Z2_0_6H2Value a))) := by
  exact contains_sound (entropyTerm_ball (Z2_0_6H2Mass_sound) Z2_0_6H2MassTermLog_sound) (by decide +kernel)
lemma Z2_0_6H2H_sound : Z2_0_6H2H.Encloses (homogeneousEntropy Z2_0_6H2Value) := by
  exact contains_sound (homogeneous_enclosed Z2_0_6H2Value Z2_0_6H2MassTerm_sound Z2_0_6H2Entropy_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Four3_0_5
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
lemma Z3_0_5Raw_sound_0 (j : Fin 6) :
    (Z3_0_5Raw (0,j)).Encloses (weight (orderedPairInteger (shape 3 0 5) 0 j) : ℝ) := by
  fin_cases j
  · change (Z3_0_5Raw (0,0)).Encloses (weight (orderedPairInteger (shape 3 0 5) 0 0) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 0 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (0,1)).Encloses (weight (orderedPairInteger (shape 3 0 5) 0 1) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 0 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (0,2)).Encloses (weight (orderedPairInteger (shape 3 0 5) 0 2) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 0 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (0,3)).Encloses (weight (orderedPairInteger (shape 3 0 5) 0 3) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 0 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (0,4)).Encloses (weight (orderedPairInteger (shape 3 0 5) 0 4) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 0 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (0,5)).Encloses (weight (orderedPairInteger (shape 3 0 5) 0 5) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 0 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z3_0_5Raw_sound_1 (j : Fin 6) :
    (Z3_0_5Raw (1,j)).Encloses (weight (orderedPairInteger (shape 3 0 5) 1 j) : ℝ) := by
  fin_cases j
  · change (Z3_0_5Raw (1,0)).Encloses (weight (orderedPairInteger (shape 3 0 5) 1 0) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 1 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (1,1)).Encloses (weight (orderedPairInteger (shape 3 0 5) 1 1) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 1 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (1,2)).Encloses (weight (orderedPairInteger (shape 3 0 5) 1 2) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 1 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (1,3)).Encloses (weight (orderedPairInteger (shape 3 0 5) 1 3) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 1 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (1,4)).Encloses (weight (orderedPairInteger (shape 3 0 5) 1 4) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 1 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (1,5)).Encloses (weight (orderedPairInteger (shape 3 0 5) 1 5) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 1 5 = (-2174) := by decide +kernel
    rw [he]
    exact w189_sound
lemma Z3_0_5Raw_sound_2 (j : Fin 6) :
    (Z3_0_5Raw (2,j)).Encloses (weight (orderedPairInteger (shape 3 0 5) 2 j) : ℝ) := by
  fin_cases j
  · change (Z3_0_5Raw (2,0)).Encloses (weight (orderedPairInteger (shape 3 0 5) 2 0) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 2 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (2,1)).Encloses (weight (orderedPairInteger (shape 3 0 5) 2 1) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 2 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (2,2)).Encloses (weight (orderedPairInteger (shape 3 0 5) 2 2) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 2 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (2,3)).Encloses (weight (orderedPairInteger (shape 3 0 5) 2 3) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 2 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (2,4)).Encloses (weight (orderedPairInteger (shape 3 0 5) 2 4) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 2 4 = (21564) := by decide +kernel
    rw [he]
    exact w202_sound
  · change (Z3_0_5Raw (2,5)).Encloses (weight (orderedPairInteger (shape 3 0 5) 2 5) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 2 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z3_0_5Raw_sound_3 (j : Fin 6) :
    (Z3_0_5Raw (3,j)).Encloses (weight (orderedPairInteger (shape 3 0 5) 3 j) : ℝ) := by
  fin_cases j
  · change (Z3_0_5Raw (3,0)).Encloses (weight (orderedPairInteger (shape 3 0 5) 3 0) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 3 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (3,1)).Encloses (weight (orderedPairInteger (shape 3 0 5) 3 1) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 3 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (3,2)).Encloses (weight (orderedPairInteger (shape 3 0 5) 3 2) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 3 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (3,3)).Encloses (weight (orderedPairInteger (shape 3 0 5) 3 3) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 3 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (3,4)).Encloses (weight (orderedPairInteger (shape 3 0 5) 3 4) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 3 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (3,5)).Encloses (weight (orderedPairInteger (shape 3 0 5) 3 5) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 3 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z3_0_5Raw_sound_4 (j : Fin 6) :
    (Z3_0_5Raw (4,j)).Encloses (weight (orderedPairInteger (shape 3 0 5) 4 j) : ℝ) := by
  fin_cases j
  · change (Z3_0_5Raw (4,0)).Encloses (weight (orderedPairInteger (shape 3 0 5) 4 0) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 4 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (4,1)).Encloses (weight (orderedPairInteger (shape 3 0 5) 4 1) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 4 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (4,2)).Encloses (weight (orderedPairInteger (shape 3 0 5) 4 2) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 4 2 = (21564) := by decide +kernel
    rw [he]
    exact w202_sound
  · change (Z3_0_5Raw (4,3)).Encloses (weight (orderedPairInteger (shape 3 0 5) 4 3) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 4 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (4,4)).Encloses (weight (orderedPairInteger (shape 3 0 5) 4 4) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 4 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (4,5)).Encloses (weight (orderedPairInteger (shape 3 0 5) 4 5) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 4 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z3_0_5Raw_sound_5 (j : Fin 6) :
    (Z3_0_5Raw (5,j)).Encloses (weight (orderedPairInteger (shape 3 0 5) 5 j) : ℝ) := by
  fin_cases j
  · change (Z3_0_5Raw (5,0)).Encloses (weight (orderedPairInteger (shape 3 0 5) 5 0) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 5 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (5,1)).Encloses (weight (orderedPairInteger (shape 3 0 5) 5 1) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 5 1 = (-2174) := by decide +kernel
    rw [he]
    exact w189_sound
  · change (Z3_0_5Raw (5,2)).Encloses (weight (orderedPairInteger (shape 3 0 5) 5 2) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 5 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (5,3)).Encloses (weight (orderedPairInteger (shape 3 0 5) 5 3) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 5 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (5,4)).Encloses (weight (orderedPairInteger (shape 3 0 5) 5 4) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 5 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (5,5)).Encloses (weight (orderedPairInteger (shape 3 0 5) 5 5) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 5 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z3_0_5Raw_sound (ij : PairSlot) :
    (Z3_0_5Raw ij).Encloses (weight (orderedPairInteger (shape 3 0 5) ij.1 ij.2) : ℝ) := by
  rcases ij with ⟨i,j⟩
  revert i
  exact forall_fin6 (Z3_0_5Raw_sound_0 j) (Z3_0_5Raw_sound_1 j) (Z3_0_5Raw_sound_2 j) (Z3_0_5Raw_sound_3 j) (Z3_0_5Raw_sound_4 j) (Z3_0_5Raw_sound_5 j)
lemma Z3_0_5Den_sound : Z3_0_5Den.Encloses
    (((orderedPairs (shape 3 0 5)).map (fun ij => weight (orderedPairInteger (shape 3 0 5) ij.1 ij.2))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (orderedPairs (shape 3 0 5)) Z3_0_5Raw
    (fun ij => weight (orderedPairInteger (shape 3 0 5) ij.1 ij.2))
    (fun ij _ => Z3_0_5Raw_sound ij)) (by decide +kernel)
lemma Z3_0_5Den_pos : 0 < Z3_0_5Den.lower := by decide +kernel
lemma Z3_0_5Contains : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j = shapeMax (shape 3 0 5) →
    contains (.mul (Z3_0_5Raw (i,j)) (.inv Z3_0_5Den)) (Z3_0_5Probs (i,j)) = true := by
  decide +kernel
lemma Z3_0_5Zero : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j ≠ shapeMax (shape 3 0 5) → Z3_0_5Probs (i,j) = .exact 0 := by
  decide +kernel
lemma Z3_0_5Probs_sound (ij : PairSlot) :
    (Z3_0_5Probs ij).Encloses (zeroPairLaw (shape 3 0 5) ij.1 ij.2 : ℝ) := by
  by_cases h : statisticWeight ij.1 + statisticWeight ij.2 = shapeMax (shape 3 0 5)
  · have hb := contains_sound (Ball.mul_sound (Z3_0_5Raw_sound ij)
      (Ball.inv_sound Z3_0_5Den_sound Z3_0_5Den_pos)) (Z3_0_5Contains ij.1 ij.2 h)
    simpa only [zeroPairLaw, h, ite_true, if_true, Rat.cast_div, Rat.cast_mul,
      Rat.cast_inv, div_eq_mul_inv] using hb
  · rw [Z3_0_5Zero ij.1 ij.2 h]
    simpa only [zeroPairLaw, h, ite_false, if_false] using Ball.exact_sound 0

lemma Z3_0_5Half_sound (w : Fin 3) (ij : PairSlot) :
    (Z3_0_5Half w ij).Encloses (halfLaw (shape 3 0 5) w ij : ℝ) := by
  have hp : positive (shape 3 0 5) = false := by decide +kernel
  simp only [Z3_0_5Half, halfLaw, hp, Bool.false_eq_true, ite_false, if_false]
  split_ifs
  · exact Ball.exact_sound 1
  · exact Ball.exact_sound 0
  · exact Z3_0_5Probs_sound _
  · exact Z3_0_5Probs_sound _

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
lemma Z3_0_5H2E_1_5Log_sound : Z3_0_5H2E_1_5Log.Encloses (Real.log (Z3_0_5H2Value ((1,5) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z3_0_5Half_sound 2) ((1,5) : PairSlot)) (w := Z3_0_5H2E_1_5LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z3_0_5H2E_1_5_sound : Z3_0_5H2E_1_5.Encloses (Foundation.entropyTerm (Z3_0_5H2Value ((1,5) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z3_0_5Half_sound 2) ((1,5) : PairSlot)) Z3_0_5H2E_1_5Log_sound) (by decide +kernel)
lemma Z3_0_5H2E_2_4Log_sound : Z3_0_5H2E_2_4Log.Encloses (Real.log (Z3_0_5H2Value ((2,4) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z3_0_5Half_sound 2) ((2,4) : PairSlot)) (w := Z3_0_5H2E_2_4LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z3_0_5H2E_2_4_sound : Z3_0_5H2E_2_4.Encloses (Foundation.entropyTerm (Z3_0_5H2Value ((2,4) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z3_0_5Half_sound 2) ((2,4) : PairSlot)) Z3_0_5H2E_2_4Log_sound) (by decide +kernel)
lemma Z3_0_5H2E_3_4Log_sound : Z3_0_5H2E_3_4Log.Encloses (Real.log (Z3_0_5H2Value ((3,4) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z3_0_5Half_sound 2) ((3,4) : PairSlot)) (w := Z3_0_5H2E_3_4LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z3_0_5H2E_3_4_sound : Z3_0_5H2E_3_4.Encloses (Foundation.entropyTerm (Z3_0_5H2Value ((3,4) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z3_0_5Half_sound 2) ((3,4) : PairSlot)) Z3_0_5H2E_3_4Log_sound) (by decide +kernel)
lemma Z3_0_5H2E_4_2Log_sound : Z3_0_5H2E_4_2Log.Encloses (Real.log (Z3_0_5H2Value ((4,2) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z3_0_5Half_sound 2) ((4,2) : PairSlot)) (w := Z3_0_5H2E_4_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z3_0_5H2E_4_2_sound : Z3_0_5H2E_4_2.Encloses (Foundation.entropyTerm (Z3_0_5H2Value ((4,2) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z3_0_5Half_sound 2) ((4,2) : PairSlot)) Z3_0_5H2E_4_2Log_sound) (by decide +kernel)
lemma Z3_0_5H2E_4_3Log_sound : Z3_0_5H2E_4_3Log.Encloses (Real.log (Z3_0_5H2Value ((4,3) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z3_0_5Half_sound 2) ((4,3) : PairSlot)) (w := Z3_0_5H2E_4_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z3_0_5H2E_4_3_sound : Z3_0_5H2E_4_3.Encloses (Foundation.entropyTerm (Z3_0_5H2Value ((4,3) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z3_0_5Half_sound 2) ((4,3) : PairSlot)) Z3_0_5H2E_4_3Log_sound) (by decide +kernel)
lemma Z3_0_5H2E_5_1Log_sound : Z3_0_5H2E_5_1Log.Encloses (Real.log (Z3_0_5H2Value ((5,1) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z3_0_5Half_sound 2) ((5,1) : PairSlot)) (w := Z3_0_5H2E_5_1LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z3_0_5H2E_5_1_sound : Z3_0_5H2E_5_1.Encloses (Foundation.entropyTerm (Z3_0_5H2Value ((5,1) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z3_0_5Half_sound 2) ((5,1) : PairSlot)) Z3_0_5H2E_5_1Log_sound) (by decide +kernel)
lemma Z3_0_5H2Terms_sound (a : PairSlot) :
    (Z3_0_5H2Terms a).Encloses (Foundation.entropyTerm (Z3_0_5H2Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((0,0) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((0,1) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((0,2) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((0,3) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((0,4) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((0,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((1,0) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((1,1) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((1,2) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((1,3) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((1,4) : PairSlot))) Z3_0_5H2E_1_5_sound
  · exact forall_fin6 (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((2,0) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((2,1) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((2,2) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((2,3) : PairSlot))) Z3_0_5H2E_2_4_sound (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((2,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((3,0) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((3,1) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((3,2) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((3,3) : PairSlot))) Z3_0_5H2E_3_4_sound (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((3,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((4,0) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((4,1) : PairSlot))) Z3_0_5H2E_4_2_sound Z3_0_5H2E_4_3_sound (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((4,4) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((4,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((5,0) : PairSlot))) Z3_0_5H2E_5_1_sound (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((5,2) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((5,3) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((5,4) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((5,5) : PairSlot)))
lemma Z3_0_5H2Entropy_sound : Z3_0_5H2Entropy.Encloses (Foundation.finiteEntropy Z3_0_5H2Value) := by
  exact contains_sound (entropyPair_enclosed Z3_0_5H2Value Z3_0_5H2Terms Z3_0_5H2Terms_sound) (by decide +kernel)
lemma Z3_0_5H2Mass_sound : Z3_0_5H2Mass.Encloses (∑ a, Z3_0_5H2Value a) := by
  exact contains_sound (pairSumBall_sound (Z3_0_5Half 2) Z3_0_5H2Value (Z3_0_5Half_sound 2)) (by decide +kernel)
lemma Z3_0_5H2MassTermLog_sound : Z3_0_5H2MassTermLog.Encloses (Real.log ((∑ a, Z3_0_5H2Value a))) := by
  exact checkLog_sound logTwoBall_sound (Z3_0_5H2Mass_sound) (w := Z3_0_5H2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z3_0_5H2MassTerm_sound : Z3_0_5H2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, Z3_0_5H2Value a))) := by
  exact contains_sound (entropyTerm_ball (Z3_0_5H2Mass_sound) Z3_0_5H2MassTermLog_sound) (by decide +kernel)
lemma Z3_0_5H2H_sound : Z3_0_5H2H.Encloses (homogeneousEntropy Z3_0_5H2Value) := by
  exact contains_sound (homogeneous_enclosed Z3_0_5H2Value Z3_0_5H2MassTerm_sound Z3_0_5H2Entropy_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitA3_6_7
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
lemma A3_6_7_below : below (shape 3 6 7) = [
  (shape 0 1 7),
  (shape 0 2 6),
  (shape 0 3 5),
  (shape 0 4 4),
  (shape 0 5 3),
  (shape 0 6 2),
  (shape 1 0 7),
  (shape 1 1 6),
  (shape 1 2 5),
  (shape 1 3 4),
  (shape 1 4 3),
  (shape 1 5 2),
  (shape 1 6 1),
  (shape 2 0 6),
  (shape 2 1 5),
  (shape 2 2 4),
  (shape 2 3 3),
  (shape 2 4 2),
  (shape 2 5 1),
  (shape 2 6 0),
  (shape 3 0 5),
  (shape 3 1 4),
  (shape 3 2 3),
  (shape 3 3 2),
  (shape 3 4 1),
  (shape 3 5 0)] := by decide +kernel

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA3_6_7I2
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
lemma CA3_6_7I2Singles_sound (u : Shape) (hu : u ∈ below (shape 3 6 7))
    (hd : designated (Equiv.refl (Fin 3)) 2 u) :
    (CA3_6_7I2Singles u).Encloses (homogeneousEntropy ((fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) u)) := by
  rw [A3_6_7_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Z0_1_7H2H_sound
  · exact Z0_2_6H2H_sound
  · exact Z0_3_5H2H_sound
  · exact Z0_4_4H2H_sound
  · exact Z0_5_3H2H_sound
  · exact Z0_6_2H2H_sound
  · exact Z1_0_7H2H_sound
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 1 6) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 2 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 3 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 4 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 5 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 6 1) by decide +kernel) hd |>.elim
  · exact Z2_0_6H2H_sound
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 2 1 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 2 2 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 2 3 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 2 4 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 2 5 1) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 2 6 0) by decide +kernel) hd |>.elim
  · exact Z3_0_5H2H_sound
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 3 1 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 3 2 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 3 3 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 3 4 1) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 3 5 0) by decide +kernel) hd |>.elim
lemma CA3_6_7I2Singleton_sound_oai : CA3_6_7I2Singleton.Encloses
    (singletonEntropy (below (shape 3 6 7)) (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 3 6 7)) A3_6_7Law (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 2
    CA3_6_7I2Singles (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_6_7Law_sound u) CA3_6_7I2Singles_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_6_7I2Singleton_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_6_7I2Singleton_sound_oai
