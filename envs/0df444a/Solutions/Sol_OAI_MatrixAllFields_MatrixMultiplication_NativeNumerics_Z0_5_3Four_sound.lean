-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z0_5_3Four_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:20:22.806819+00:00
-- url     : https://prove2.me/submissions/0824bd0e-d47e-4fea-86e3-a3f8ed461e7d

import Mathlib
import Definitions.Def_OAIQ254M006
import Definitions.Def_OAIQ254M007
import Definitions.Def_OAIQ254M011
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_inv_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_mul_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkLog_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkPolynomial_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_finSumBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_Z0_5_3Entropy_sound

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

lemma log_exact_one_ball {p : ℝ} (hp : (Ball.exact 1).Encloses p) :
    (Ball.exact 0).Encloses (Real.log p) := by
  have hb := Ball.bounds hp
  have h : p = 1 := by norm_num [Ball.lower, Ball.upper, Ball.exact] at hb <;> linarith
  rw [h, Real.log_one]
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
lemma logN1_sound : logN1.Encloses (Real.log ((1 : ℝ))) := by
  exact log_exact_one_ball ((by convert Ball.exact_sound (1 : ℚ) using 1; norm_num))
lemma logN2_sound : logN2.Encloses (Real.log ((2 : ℝ))) := by
  exact checkLog_sound logTwoBall_sound ((by convert Ball.exact_sound (2 : ℚ) using 1; norm_num)) (w := logN2Witness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma logN4_sound : logN4.Encloses (Real.log ((4 : ℝ))) := by
  exact checkLog_sound logTwoBall_sound ((by convert Ball.exact_sound (4 : ℚ) using 1; norm_num)) (w := logN4Witness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma logN10_sound : logN10.Encloses (Real.log ((10 : ℝ))) := by
  exact checkLog_sound logTwoBall_sound ((by convert Ball.exact_sound (10 : ℚ) using 1; norm_num)) (w := logN10Witness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma logN20_sound : logN20.Encloses (Real.log ((20 : ℝ))) := by
  exact checkLog_sound logTwoBall_sound ((by convert Ball.exact_sound (20 : ℚ) using 1; norm_num)) (w := logN20Witness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma logN25_sound : logN25.Encloses (Real.log ((25 : ℝ))) := by
  exact checkLog_sound logTwoBall_sound ((by convert Ball.exact_sound (25 : ℚ) using 1; norm_num)) (w := logN25Witness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma logN50_sound : logN50.Encloses (Real.log ((50 : ℝ))) := by
  exact checkLog_sound logTwoBall_sound ((by convert Ball.exact_sound (50 : ℚ) using 1; norm_num)) (w := logN50Witness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma logN100_sound : logN100.Encloses (Real.log ((100 : ℝ))) := by
  exact checkLog_sound logTwoBall_sound ((by convert Ball.exact_sound (100 : ℚ) using 1; norm_num)) (w := logN100Witness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma logN250_sound : logN250.Encloses (Real.log ((250 : ℝ))) := by
  exact checkLog_sound logTwoBall_sound ((by convert Ball.exact_sound (250 : ℚ) using 1; norm_num)) (w := logN250Witness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma logN625_sound : logN625.Encloses (Real.log ((625 : ℝ))) := by
  exact checkLog_sound logTwoBall_sound ((by convert Ball.exact_sound (625 : ℚ) using 1; norm_num)) (w := logN625Witness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma multLogs_sound (a : PairSlot) :
    (multLogs a).Encloses (Real.log (AllFieldParameters.multiplicity a.1 * AllFieldParameters.multiplicity a.2 : ℕ)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · apply forall_fin6
    · have he : AllFieldParameters.multiplicity 0 * AllFieldParameters.multiplicity 0 = 1 := by decide +kernel
      change (multLogs (0,0)).Encloses (Real.log (AllFieldParameters.multiplicity 0 * AllFieldParameters.multiplicity 0 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN1_sound
    · have he : AllFieldParameters.multiplicity 0 * AllFieldParameters.multiplicity 1 = 10 := by decide +kernel
      change (multLogs (0,1)).Encloses (Real.log (AllFieldParameters.multiplicity 0 * AllFieldParameters.multiplicity 1 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN10_sound
    · have he : AllFieldParameters.multiplicity 0 * AllFieldParameters.multiplicity 2 = 25 := by decide +kernel
      change (multLogs (0,2)).Encloses (Real.log (AllFieldParameters.multiplicity 0 * AllFieldParameters.multiplicity 2 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN25_sound
    · have he : AllFieldParameters.multiplicity 0 * AllFieldParameters.multiplicity 3 = 2 := by decide +kernel
      change (multLogs (0,3)).Encloses (Real.log (AllFieldParameters.multiplicity 0 * AllFieldParameters.multiplicity 3 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN2_sound
    · have he : AllFieldParameters.multiplicity 0 * AllFieldParameters.multiplicity 4 = 10 := by decide +kernel
      change (multLogs (0,4)).Encloses (Real.log (AllFieldParameters.multiplicity 0 * AllFieldParameters.multiplicity 4 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN10_sound
    · have he : AllFieldParameters.multiplicity 0 * AllFieldParameters.multiplicity 5 = 1 := by decide +kernel
      change (multLogs (0,5)).Encloses (Real.log (AllFieldParameters.multiplicity 0 * AllFieldParameters.multiplicity 5 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN1_sound
  · apply forall_fin6
    · have he : AllFieldParameters.multiplicity 1 * AllFieldParameters.multiplicity 0 = 10 := by decide +kernel
      change (multLogs (1,0)).Encloses (Real.log (AllFieldParameters.multiplicity 1 * AllFieldParameters.multiplicity 0 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN10_sound
    · have he : AllFieldParameters.multiplicity 1 * AllFieldParameters.multiplicity 1 = 100 := by decide +kernel
      change (multLogs (1,1)).Encloses (Real.log (AllFieldParameters.multiplicity 1 * AllFieldParameters.multiplicity 1 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN100_sound
    · have he : AllFieldParameters.multiplicity 1 * AllFieldParameters.multiplicity 2 = 250 := by decide +kernel
      change (multLogs (1,2)).Encloses (Real.log (AllFieldParameters.multiplicity 1 * AllFieldParameters.multiplicity 2 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN250_sound
    · have he : AllFieldParameters.multiplicity 1 * AllFieldParameters.multiplicity 3 = 20 := by decide +kernel
      change (multLogs (1,3)).Encloses (Real.log (AllFieldParameters.multiplicity 1 * AllFieldParameters.multiplicity 3 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN20_sound
    · have he : AllFieldParameters.multiplicity 1 * AllFieldParameters.multiplicity 4 = 100 := by decide +kernel
      change (multLogs (1,4)).Encloses (Real.log (AllFieldParameters.multiplicity 1 * AllFieldParameters.multiplicity 4 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN100_sound
    · have he : AllFieldParameters.multiplicity 1 * AllFieldParameters.multiplicity 5 = 10 := by decide +kernel
      change (multLogs (1,5)).Encloses (Real.log (AllFieldParameters.multiplicity 1 * AllFieldParameters.multiplicity 5 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN10_sound
  · apply forall_fin6
    · have he : AllFieldParameters.multiplicity 2 * AllFieldParameters.multiplicity 0 = 25 := by decide +kernel
      change (multLogs (2,0)).Encloses (Real.log (AllFieldParameters.multiplicity 2 * AllFieldParameters.multiplicity 0 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN25_sound
    · have he : AllFieldParameters.multiplicity 2 * AllFieldParameters.multiplicity 1 = 250 := by decide +kernel
      change (multLogs (2,1)).Encloses (Real.log (AllFieldParameters.multiplicity 2 * AllFieldParameters.multiplicity 1 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN250_sound
    · have he : AllFieldParameters.multiplicity 2 * AllFieldParameters.multiplicity 2 = 625 := by decide +kernel
      change (multLogs (2,2)).Encloses (Real.log (AllFieldParameters.multiplicity 2 * AllFieldParameters.multiplicity 2 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN625_sound
    · have he : AllFieldParameters.multiplicity 2 * AllFieldParameters.multiplicity 3 = 50 := by decide +kernel
      change (multLogs (2,3)).Encloses (Real.log (AllFieldParameters.multiplicity 2 * AllFieldParameters.multiplicity 3 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN50_sound
    · have he : AllFieldParameters.multiplicity 2 * AllFieldParameters.multiplicity 4 = 250 := by decide +kernel
      change (multLogs (2,4)).Encloses (Real.log (AllFieldParameters.multiplicity 2 * AllFieldParameters.multiplicity 4 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN250_sound
    · have he : AllFieldParameters.multiplicity 2 * AllFieldParameters.multiplicity 5 = 25 := by decide +kernel
      change (multLogs (2,5)).Encloses (Real.log (AllFieldParameters.multiplicity 2 * AllFieldParameters.multiplicity 5 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN25_sound
  · apply forall_fin6
    · have he : AllFieldParameters.multiplicity 3 * AllFieldParameters.multiplicity 0 = 2 := by decide +kernel
      change (multLogs (3,0)).Encloses (Real.log (AllFieldParameters.multiplicity 3 * AllFieldParameters.multiplicity 0 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN2_sound
    · have he : AllFieldParameters.multiplicity 3 * AllFieldParameters.multiplicity 1 = 20 := by decide +kernel
      change (multLogs (3,1)).Encloses (Real.log (AllFieldParameters.multiplicity 3 * AllFieldParameters.multiplicity 1 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN20_sound
    · have he : AllFieldParameters.multiplicity 3 * AllFieldParameters.multiplicity 2 = 50 := by decide +kernel
      change (multLogs (3,2)).Encloses (Real.log (AllFieldParameters.multiplicity 3 * AllFieldParameters.multiplicity 2 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN50_sound
    · have he : AllFieldParameters.multiplicity 3 * AllFieldParameters.multiplicity 3 = 4 := by decide +kernel
      change (multLogs (3,3)).Encloses (Real.log (AllFieldParameters.multiplicity 3 * AllFieldParameters.multiplicity 3 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN4_sound
    · have he : AllFieldParameters.multiplicity 3 * AllFieldParameters.multiplicity 4 = 20 := by decide +kernel
      change (multLogs (3,4)).Encloses (Real.log (AllFieldParameters.multiplicity 3 * AllFieldParameters.multiplicity 4 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN20_sound
    · have he : AllFieldParameters.multiplicity 3 * AllFieldParameters.multiplicity 5 = 2 := by decide +kernel
      change (multLogs (3,5)).Encloses (Real.log (AllFieldParameters.multiplicity 3 * AllFieldParameters.multiplicity 5 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN2_sound
  · apply forall_fin6
    · have he : AllFieldParameters.multiplicity 4 * AllFieldParameters.multiplicity 0 = 10 := by decide +kernel
      change (multLogs (4,0)).Encloses (Real.log (AllFieldParameters.multiplicity 4 * AllFieldParameters.multiplicity 0 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN10_sound
    · have he : AllFieldParameters.multiplicity 4 * AllFieldParameters.multiplicity 1 = 100 := by decide +kernel
      change (multLogs (4,1)).Encloses (Real.log (AllFieldParameters.multiplicity 4 * AllFieldParameters.multiplicity 1 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN100_sound
    · have he : AllFieldParameters.multiplicity 4 * AllFieldParameters.multiplicity 2 = 250 := by decide +kernel
      change (multLogs (4,2)).Encloses (Real.log (AllFieldParameters.multiplicity 4 * AllFieldParameters.multiplicity 2 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN250_sound
    · have he : AllFieldParameters.multiplicity 4 * AllFieldParameters.multiplicity 3 = 20 := by decide +kernel
      change (multLogs (4,3)).Encloses (Real.log (AllFieldParameters.multiplicity 4 * AllFieldParameters.multiplicity 3 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN20_sound
    · have he : AllFieldParameters.multiplicity 4 * AllFieldParameters.multiplicity 4 = 100 := by decide +kernel
      change (multLogs (4,4)).Encloses (Real.log (AllFieldParameters.multiplicity 4 * AllFieldParameters.multiplicity 4 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN100_sound
    · have he : AllFieldParameters.multiplicity 4 * AllFieldParameters.multiplicity 5 = 10 := by decide +kernel
      change (multLogs (4,5)).Encloses (Real.log (AllFieldParameters.multiplicity 4 * AllFieldParameters.multiplicity 5 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN10_sound
  · apply forall_fin6
    · have he : AllFieldParameters.multiplicity 5 * AllFieldParameters.multiplicity 0 = 1 := by decide +kernel
      change (multLogs (5,0)).Encloses (Real.log (AllFieldParameters.multiplicity 5 * AllFieldParameters.multiplicity 0 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN1_sound
    · have he : AllFieldParameters.multiplicity 5 * AllFieldParameters.multiplicity 1 = 10 := by decide +kernel
      change (multLogs (5,1)).Encloses (Real.log (AllFieldParameters.multiplicity 5 * AllFieldParameters.multiplicity 1 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN10_sound
    · have he : AllFieldParameters.multiplicity 5 * AllFieldParameters.multiplicity 2 = 25 := by decide +kernel
      change (multLogs (5,2)).Encloses (Real.log (AllFieldParameters.multiplicity 5 * AllFieldParameters.multiplicity 2 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN25_sound
    · have he : AllFieldParameters.multiplicity 5 * AllFieldParameters.multiplicity 3 = 2 := by decide +kernel
      change (multLogs (5,3)).Encloses (Real.log (AllFieldParameters.multiplicity 5 * AllFieldParameters.multiplicity 3 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN2_sound
    · have he : AllFieldParameters.multiplicity 5 * AllFieldParameters.multiplicity 4 = 10 := by decide +kernel
      change (multLogs (5,4)).Encloses (Real.log (AllFieldParameters.multiplicity 5 * AllFieldParameters.multiplicity 4 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN10_sound
    · have he : AllFieldParameters.multiplicity 5 * AllFieldParameters.multiplicity 5 = 1 := by decide +kernel
      change (multLogs (5,5)).Encloses (Real.log (AllFieldParameters.multiplicity 5 * AllFieldParameters.multiplicity 5 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN1_sound

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
lemma w158_sound : w158.Encloses (weight (-6216) : ℝ) := by
  exact weight_enclosed_of_trace (-6216) w158Trace w158S0 w158S1 w158S2 w158S3 w158S4 w158S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

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
lemma w211_sound : w211.Encloses (weight (23895) : ℝ) := by
  exact weight_enclosed_of_trace (23895) w211Trace w211S0 w211S1 w211S2 w211S3 w211S4 w211S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Four0_5_3
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
lemma Z0_5_3Raw_sound_0 (j : Fin 6) :
    (Z0_5_3Raw (0,j)).Encloses (weight (orderedPairInteger (shape 0 5 3) 0 j) : ℝ) := by
  fin_cases j
  · change (Z0_5_3Raw (0,0)).Encloses (weight (orderedPairInteger (shape 0 5 3) 0 0) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 0 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (0,1)).Encloses (weight (orderedPairInteger (shape 0 5 3) 0 1) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 0 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (0,2)).Encloses (weight (orderedPairInteger (shape 0 5 3) 0 2) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 0 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (0,3)).Encloses (weight (orderedPairInteger (shape 0 5 3) 0 3) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 0 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (0,4)).Encloses (weight (orderedPairInteger (shape 0 5 3) 0 4) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 0 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (0,5)).Encloses (weight (orderedPairInteger (shape 0 5 3) 0 5) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 0 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_5_3Raw_sound_1 (j : Fin 6) :
    (Z0_5_3Raw (1,j)).Encloses (weight (orderedPairInteger (shape 0 5 3) 1 j) : ℝ) := by
  fin_cases j
  · change (Z0_5_3Raw (1,0)).Encloses (weight (orderedPairInteger (shape 0 5 3) 1 0) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 1 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (1,1)).Encloses (weight (orderedPairInteger (shape 0 5 3) 1 1) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 1 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (1,2)).Encloses (weight (orderedPairInteger (shape 0 5 3) 1 2) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 1 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (1,3)).Encloses (weight (orderedPairInteger (shape 0 5 3) 1 3) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 1 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (1,4)).Encloses (weight (orderedPairInteger (shape 0 5 3) 1 4) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 1 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (1,5)).Encloses (weight (orderedPairInteger (shape 0 5 3) 1 5) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 1 5 = (-6216) := by decide +kernel
    rw [he]
    exact w158_sound
lemma Z0_5_3Raw_sound_2 (j : Fin 6) :
    (Z0_5_3Raw (2,j)).Encloses (weight (orderedPairInteger (shape 0 5 3) 2 j) : ℝ) := by
  fin_cases j
  · change (Z0_5_3Raw (2,0)).Encloses (weight (orderedPairInteger (shape 0 5 3) 2 0) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 2 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (2,1)).Encloses (weight (orderedPairInteger (shape 0 5 3) 2 1) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 2 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (2,2)).Encloses (weight (orderedPairInteger (shape 0 5 3) 2 2) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 2 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (2,3)).Encloses (weight (orderedPairInteger (shape 0 5 3) 2 3) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 2 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (2,4)).Encloses (weight (orderedPairInteger (shape 0 5 3) 2 4) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 2 4 = (23895) := by decide +kernel
    rw [he]
    exact w211_sound
  · change (Z0_5_3Raw (2,5)).Encloses (weight (orderedPairInteger (shape 0 5 3) 2 5) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 2 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_5_3Raw_sound_3 (j : Fin 6) :
    (Z0_5_3Raw (3,j)).Encloses (weight (orderedPairInteger (shape 0 5 3) 3 j) : ℝ) := by
  fin_cases j
  · change (Z0_5_3Raw (3,0)).Encloses (weight (orderedPairInteger (shape 0 5 3) 3 0) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 3 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (3,1)).Encloses (weight (orderedPairInteger (shape 0 5 3) 3 1) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 3 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (3,2)).Encloses (weight (orderedPairInteger (shape 0 5 3) 3 2) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 3 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (3,3)).Encloses (weight (orderedPairInteger (shape 0 5 3) 3 3) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 3 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (3,4)).Encloses (weight (orderedPairInteger (shape 0 5 3) 3 4) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 3 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (3,5)).Encloses (weight (orderedPairInteger (shape 0 5 3) 3 5) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 3 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_5_3Raw_sound_4 (j : Fin 6) :
    (Z0_5_3Raw (4,j)).Encloses (weight (orderedPairInteger (shape 0 5 3) 4 j) : ℝ) := by
  fin_cases j
  · change (Z0_5_3Raw (4,0)).Encloses (weight (orderedPairInteger (shape 0 5 3) 4 0) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 4 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (4,1)).Encloses (weight (orderedPairInteger (shape 0 5 3) 4 1) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 4 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (4,2)).Encloses (weight (orderedPairInteger (shape 0 5 3) 4 2) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 4 2 = (23895) := by decide +kernel
    rw [he]
    exact w211_sound
  · change (Z0_5_3Raw (4,3)).Encloses (weight (orderedPairInteger (shape 0 5 3) 4 3) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 4 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (4,4)).Encloses (weight (orderedPairInteger (shape 0 5 3) 4 4) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 4 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (4,5)).Encloses (weight (orderedPairInteger (shape 0 5 3) 4 5) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 4 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_5_3Raw_sound_5 (j : Fin 6) :
    (Z0_5_3Raw (5,j)).Encloses (weight (orderedPairInteger (shape 0 5 3) 5 j) : ℝ) := by
  fin_cases j
  · change (Z0_5_3Raw (5,0)).Encloses (weight (orderedPairInteger (shape 0 5 3) 5 0) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 5 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (5,1)).Encloses (weight (orderedPairInteger (shape 0 5 3) 5 1) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 5 1 = (-6216) := by decide +kernel
    rw [he]
    exact w158_sound
  · change (Z0_5_3Raw (5,2)).Encloses (weight (orderedPairInteger (shape 0 5 3) 5 2) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 5 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (5,3)).Encloses (weight (orderedPairInteger (shape 0 5 3) 5 3) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 5 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (5,4)).Encloses (weight (orderedPairInteger (shape 0 5 3) 5 4) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 5 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (5,5)).Encloses (weight (orderedPairInteger (shape 0 5 3) 5 5) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 5 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_5_3Raw_sound (ij : PairSlot) :
    (Z0_5_3Raw ij).Encloses (weight (orderedPairInteger (shape 0 5 3) ij.1 ij.2) : ℝ) := by
  rcases ij with ⟨i,j⟩
  revert i
  exact forall_fin6 (Z0_5_3Raw_sound_0 j) (Z0_5_3Raw_sound_1 j) (Z0_5_3Raw_sound_2 j) (Z0_5_3Raw_sound_3 j) (Z0_5_3Raw_sound_4 j) (Z0_5_3Raw_sound_5 j)
lemma Z0_5_3Den_sound : Z0_5_3Den.Encloses
    (((orderedPairs (shape 0 5 3)).map (fun ij => weight (orderedPairInteger (shape 0 5 3) ij.1 ij.2))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (orderedPairs (shape 0 5 3)) Z0_5_3Raw
    (fun ij => weight (orderedPairInteger (shape 0 5 3) ij.1 ij.2))
    (fun ij _ => Z0_5_3Raw_sound ij)) (by decide +kernel)
lemma Z0_5_3Den_pos : 0 < Z0_5_3Den.lower := by decide +kernel
lemma Z0_5_3Contains : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j = shapeMax (shape 0 5 3) →
    contains (.mul (Z0_5_3Raw (i,j)) (.inv Z0_5_3Den)) (Z0_5_3Probs (i,j)) = true := by
  decide +kernel
lemma Z0_5_3Zero : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j ≠ shapeMax (shape 0 5 3) → Z0_5_3Probs (i,j) = .exact 0 := by
  decide +kernel
lemma Z0_5_3Probs_sound (ij : PairSlot) :
    (Z0_5_3Probs ij).Encloses (zeroPairLaw (shape 0 5 3) ij.1 ij.2 : ℝ) := by
  by_cases h : statisticWeight ij.1 + statisticWeight ij.2 = shapeMax (shape 0 5 3)
  · have hb := contains_sound (Ball.mul_sound (Z0_5_3Raw_sound ij)
      (Ball.inv_sound Z0_5_3Den_sound Z0_5_3Den_pos)) (Z0_5_3Contains ij.1 ij.2 h)
    simpa only [zeroPairLaw, h, ite_true, if_true, Rat.cast_div, Rat.cast_mul,
      Rat.cast_inv, div_eq_mul_inv] using hb
  · rw [Z0_5_3Zero ij.1 ij.2 h]
    simpa only [zeroPairLaw, h, ite_false, if_false] using Ball.exact_sound 0

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
lemma Z0_5_3Labels_sound : Z0_5_3Labels.Encloses
    (∑ a : PairSlot, (zeroPairLaw (shape 0 5 3) a.1 a.2 : ℝ) *
      Real.log (AllFieldParameters.multiplicity a.1 * AllFieldParameters.multiplicity a.2 : ℕ)) := by
  exact contains_sound (pairSumBall_sound (fun a => .mul (Z0_5_3Probs a) (multLogs a))
    _ (fun a => Ball.mul_sound (Z0_5_3Probs_sound a) (multLogs_sound a))) (by decide +kernel)
lemma Z0_5_3Four_sound_oai : Z0_5_3Four.Encloses (AllFieldZeroLeafRates.fourRate (shape 0 5 3)) := by
  exact contains_sound (Ball.add_sound Z0_5_3Entropy_sound Z0_5_3Labels_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z0_5_3Four_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z0_5_3Four_sound_oai
