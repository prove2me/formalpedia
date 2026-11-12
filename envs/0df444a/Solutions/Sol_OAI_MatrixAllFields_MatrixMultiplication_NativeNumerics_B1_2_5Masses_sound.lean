-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_2_5Masses_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T06:02:08.235334+00:00
-- url     : https://prove2.me/submissions/63e4359b-0d5a-4579-8b14-97cbc667f3f5

import Mathlib
import Definitions.Def_OAIQ254M002
import Definitions.Def_OAIQ254M003
import Definitions.Def_OAIQ254M005
import Definitions.Def_OAIQ254M006
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_AProbsTable_sound

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

theorem checkPolynomial_sound {t : Ball} {x : ℝ} (hx : t.Encloses x)
    (as : List ℚ) (trace : List Ball)
    (h : checkPolynomial t as trace = true) :
    (traceHead trace).Encloses (polynomial x as) := by
  induction as generalizing trace with
  | nil =>
      cases trace with
      | nil => simpa [traceHead, polynomial] using Ball.exact_sound 0
      | cons b bs => simp [checkPolynomial] at h
  | cons a as ih =>
      cases trace with
      | nil => simp [checkPolynomial] at h
      | cons b bs =>
          simp only [checkPolynomial, Bool.and_eq_true] at h
          exact contains_sound
            (Ball.add_sound (Ball.exact_sound a) (Ball.mul_sound hx (ih bs h.2))) h.1

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

lemma weight_enclosed_0 : weightSquare0_6.Encloses (weight (-55839) : ℝ) := by
  exact weight_enclosed_of_trace (-55839) weightTrace0 weightSquare0_1 weightSquare0_2 weightSquare0_3 weightSquare0_4 weightSquare0_5 weightSquare0_6
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma weight_enclosed_1 : weightSquare1_6.Encloses (weight (-36137) : ℝ) := by
  exact weight_enclosed_of_trace (-36137) weightTrace1 weightSquare1_1 weightSquare1_2 weightSquare1_3 weightSquare1_4 weightSquare1_5 weightSquare1_6
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma weight_enclosed_2 : weightSquare2_6.Encloses (weight (-17449) : ℝ) := by
  exact weight_enclosed_of_trace (-17449) weightTrace2 weightSquare2_1 weightSquare2_2 weightSquare2_3 weightSquare2_4 weightSquare2_5 weightSquare2_6
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma weight_enclosed_3 : weightSquare3_6.Encloses (weight (-1780) : ℝ) := by
  exact weight_enclosed_of_trace (-1780) weightTrace3 weightSquare3_1 weightSquare3_2 weightSquare3_3 weightSquare3_4 weightSquare3_5 weightSquare3_6
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma weight_enclosed_4 : weightSquare4_6.Encloses (weight (11561) : ℝ) := by
  exact weight_enclosed_of_trace (11561) weightTrace4 weightSquare4_1 weightSquare4_2 weightSquare4_3 weightSquare4_4 weightSquare4_5 weightSquare4_6
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma weight_enclosed_5 : weightSquare5_6.Encloses (weight (22640) : ℝ) := by
  exact weight_enclosed_of_trace (22640) weightTrace5 weightSquare5_1 weightSquare5_2 weightSquare5_3 weightSquare5_4 weightSquare5_5 weightSquare5_6
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma weight_enclosed_6 : weightSquare6_6.Encloses (weight (31188) : ℝ) := by
  exact weight_enclosed_of_trace (31188) weightTrace6 weightSquare6_1 weightSquare6_2 weightSquare6_3 weightSquare6_4 weightSquare6_5 weightSquare6_6
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma weight_enclosed_7 : weightSquare7_6.Encloses (weight (36731) : ℝ) := by
  exact weight_enclosed_of_trace (36731) weightTrace7 weightSquare7_1 weightSquare7_2 weightSquare7_3 weightSquare7_4 weightSquare7_5 weightSquare7_6
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma weight_enclosed_8 : weightSquare8_6.Encloses (weight (38593) : ℝ) := by
  exact weight_enclosed_of_trace (38593) weightTrace8 weightSquare8_1 weightSquare8_2 weightSquare8_3 weightSquare8_4 weightSquare8_5 weightSquare8_6
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma weight_enclosed_9 : weightSquare9_6.Encloses (weight (35898) : ℝ) := by
  exact weight_enclosed_of_trace (35898) weightTrace9 weightSquare9_1 weightSquare9_2 weightSquare9_3 weightSquare9_4 weightSquare9_5 weightSquare9_6
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma weight_enclosed_10 : weightSquare10_6.Encloses (weight (29051) : ℝ) := by
  exact weight_enclosed_of_trace (29051) weightTrace10 weightSquare10_1 weightSquare10_2 weightSquare10_3 weightSquare10_4 weightSquare10_5 weightSquare10_6
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma weight_enclosed_11 : weightSquare11_6.Encloses (weight (18387) : ℝ) := by
  exact weight_enclosed_of_trace (18387) weightTrace11 weightSquare11_1 weightSquare11_2 weightSquare11_3 weightSquare11_4 weightSquare11_5 weightSquare11_6
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma weight_enclosed_12 : weightSquare12_6.Encloses (weight (3823) : ℝ) := by
  exact weight_enclosed_of_trace (3823) weightTrace12 weightSquare12_1 weightSquare12_2 weightSquare12_3 weightSquare12_4 weightSquare12_5 weightSquare12_6
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma weight_enclosed_13 : weightSquare13_6.Encloses (weight (-14569) : ℝ) := by
  exact weight_enclosed_of_trace (-14569) weightTrace13 weightSquare13_1 weightSquare13_2 weightSquare13_3 weightSquare13_4 weightSquare13_5 weightSquare13_6
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma weight_enclosed_14 : weightSquare14_6.Encloses (weight (-39776) : ℝ) := by
  exact weight_enclosed_of_trace (-39776) weightTrace14 weightSquare14_1 weightSquare14_2 weightSquare14_3 weightSquare14_4 weightSquare14_5 weightSquare14_6
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma weight_enclosed_15 : weightSquare15_6.Encloses (weight (-38598) : ℝ) := by
  exact weight_enclosed_of_trace (-38598) weightTrace15 weightSquare15_1 weightSquare15_2 weightSquare15_3 weightSquare15_4 weightSquare15_5 weightSquare15_6
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma weight_enclosed_16 : weightSquare16_6.Encloses (weight (-23708) : ℝ) := by
  exact weight_enclosed_of_trace (-23708) weightTrace16 weightSquare16_1 weightSquare16_2 weightSquare16_3 weightSquare16_4 weightSquare16_5 weightSquare16_6
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma weightBall_sound (k : Fin 17) :
    (weightBall k).Encloses (weight (initialInteger k.val) : ℝ) := by
  fin_cases k
  · exact weight_enclosed_0
  · exact weight_enclosed_1
  · exact weight_enclosed_2
  · exact weight_enclosed_3
  · exact weight_enclosed_4
  · exact weight_enclosed_5
  · exact weight_enclosed_6
  · exact weight_enclosed_7
  · exact weight_enclosed_8
  · exact weight_enclosed_9
  · exact weight_enclosed_10
  · exact weight_enclosed_11
  · exact weight_enclosed_12
  · exact weight_enclosed_13
  · exact weight_enclosed_14
  · exact weight_enclosed_15
  · exact weight_enclosed_16

lemma sourceWeightBall_sound (k : ℕ) (hk : k < 17) :
    (sourceWeightBall k).Encloses (weight (initialInteger k) : ℝ) := by
  simpa only [sourceWeightBall, Nat.mod_eq_of_lt hk] using weightBall_sound ⟨k,hk⟩

lemma listSumBall_sound {α : Type*} (xs : List α) (b : α → Ball) (v : α → ℝ)
    (h : ∀ x ∈ xs, (b x).Encloses (v x)) :
    (listSumBall xs b).Encloses ((xs.map v).sum) := by
  induction xs with
  | nil => simpa [listSumBall] using Ball.exact_sound 0
  | cons x xs ih =>
    simpa only [listSumBall, List.foldr_cons, List.map_cons, List.sum_cons] using
      Ball.add_sound (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

lemma initial_shape_bound : ∀ s ∈ sortedInitial, ∀ i : Fin 3, s i < 17 := by
  decide +kernel

lemma initialRawBall_sound (s : Shape) (hs : s ∈ sortedInitial) :
    (initialRawBall s).Encloses (initialWeight s : ℝ) := by
  have h := Ball.mul_sound (Ball.exact_sound (initialMultiplicity s : ℚ))
    (Ball.mul_sound (sourceWeightBall_sound (s 0) (initial_shape_bound s hs 0))
      (Ball.mul_sound (sourceWeightBall_sound (s 1) (initial_shape_bound s hs 1))
        (sourceWeightBall_sound (s 2) (initial_shape_bound s hs 2))))
  simpa only [initialRawBall, initialWeight, Rat.cast_mul, Rat.cast_prod,
    Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two] using h

lemma initialDenominatorBall_sound :
    initialDenominatorBall.Encloses ((sortedInitial.map initialWeight).sum : ℝ) := by
  have h := listSumBall_sound sortedInitial initialRawBall
    (fun s => (initialWeight s : ℝ)) initialRawBall_sound
  simpa only [initialDenominatorBall, Rat.cast_list_sum, List.map_map,
    Function.comp_def] using h

lemma initialDenominatorBall_positive : 0 < initialDenominatorBall.lower := by
  decide +kernel

lemma initialLawBall_sound (s : Shape) (hs : s ∈ sortedInitial) :
    (initialLawBall s).Encloses (initialLaw s : ℝ) := by
  have h := Ball.mul_sound (initialRawBall_sound s hs)
    (Ball.inv_sound initialDenominatorBall_sound initialDenominatorBall_positive)
  simpa only [initialLawBall, initialLaw, hs, ite_true, if_true, Rat.cast_div,
    div_eq_mul_inv, Rat.cast_mul, Rat.cast_inv] using h

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
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_InitialProbabilities
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
lemma sortedInitial_list : sortedInitial = [
  (shape 0 0 16),
  (shape 0 1 15),
  (shape 0 2 14),
  (shape 0 3 13),
  (shape 0 4 12),
  (shape 0 5 11),
  (shape 0 6 10),
  (shape 0 7 9),
  (shape 0 8 8),
  (shape 1 1 14),
  (shape 1 2 13),
  (shape 1 3 12),
  (shape 1 4 11),
  (shape 1 5 10),
  (shape 1 6 9),
  (shape 1 7 8),
  (shape 2 2 12),
  (shape 2 3 11),
  (shape 2 4 10),
  (shape 2 5 9),
  (shape 2 6 8),
  (shape 2 7 7),
  (shape 3 3 10),
  (shape 3 4 9),
  (shape 3 5 8),
  (shape 3 6 7),
  (shape 4 4 8),
  (shape 4 5 7),
  (shape 4 6 6),
  (shape 5 5 6)] := by decide +kernel
lemma initialProbs_0_0_16 : (initialProbs (shape 0 0 16)).Encloses (initialLaw (shape 0 0 16) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 0 0 16) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_0_1_15 : (initialProbs (shape 0 1 15)).Encloses (initialLaw (shape 0 1 15) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 0 1 15) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_0_2_14 : (initialProbs (shape 0 2 14)).Encloses (initialLaw (shape 0 2 14) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 0 2 14) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_0_3_13 : (initialProbs (shape 0 3 13)).Encloses (initialLaw (shape 0 3 13) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 0 3 13) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_0_4_12 : (initialProbs (shape 0 4 12)).Encloses (initialLaw (shape 0 4 12) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 0 4 12) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_0_5_11 : (initialProbs (shape 0 5 11)).Encloses (initialLaw (shape 0 5 11) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 0 5 11) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_0_6_10 : (initialProbs (shape 0 6 10)).Encloses (initialLaw (shape 0 6 10) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 0 6 10) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_0_7_9 : (initialProbs (shape 0 7 9)).Encloses (initialLaw (shape 0 7 9) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 0 7 9) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_0_8_8 : (initialProbs (shape 0 8 8)).Encloses (initialLaw (shape 0 8 8) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 0 8 8) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_1_1_14 : (initialProbs (shape 1 1 14)).Encloses (initialLaw (shape 1 1 14) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 1 1 14) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_1_2_13 : (initialProbs (shape 1 2 13)).Encloses (initialLaw (shape 1 2 13) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 1 2 13) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_1_3_12 : (initialProbs (shape 1 3 12)).Encloses (initialLaw (shape 1 3 12) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 1 3 12) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_1_4_11 : (initialProbs (shape 1 4 11)).Encloses (initialLaw (shape 1 4 11) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 1 4 11) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_1_5_10 : (initialProbs (shape 1 5 10)).Encloses (initialLaw (shape 1 5 10) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 1 5 10) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_1_6_9 : (initialProbs (shape 1 6 9)).Encloses (initialLaw (shape 1 6 9) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 1 6 9) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_1_7_8 : (initialProbs (shape 1 7 8)).Encloses (initialLaw (shape 1 7 8) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 1 7 8) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_2_2_12 : (initialProbs (shape 2 2 12)).Encloses (initialLaw (shape 2 2 12) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 2 2 12) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_2_3_11 : (initialProbs (shape 2 3 11)).Encloses (initialLaw (shape 2 3 11) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 2 3 11) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_2_4_10 : (initialProbs (shape 2 4 10)).Encloses (initialLaw (shape 2 4 10) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 2 4 10) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_2_5_9 : (initialProbs (shape 2 5 9)).Encloses (initialLaw (shape 2 5 9) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 2 5 9) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_2_6_8 : (initialProbs (shape 2 6 8)).Encloses (initialLaw (shape 2 6 8) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 2 6 8) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_2_7_7 : (initialProbs (shape 2 7 7)).Encloses (initialLaw (shape 2 7 7) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 2 7 7) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_3_3_10 : (initialProbs (shape 3 3 10)).Encloses (initialLaw (shape 3 3 10) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 3 3 10) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_3_4_9 : (initialProbs (shape 3 4 9)).Encloses (initialLaw (shape 3 4 9) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 3 4 9) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_3_5_8 : (initialProbs (shape 3 5 8)).Encloses (initialLaw (shape 3 5 8) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 3 5 8) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_3_6_7 : (initialProbs (shape 3 6 7)).Encloses (initialLaw (shape 3 6 7) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 3 6 7) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_4_4_8 : (initialProbs (shape 4 4 8)).Encloses (initialLaw (shape 4 4 8) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 4 4 8) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_4_5_7 : (initialProbs (shape 4 5 7)).Encloses (initialLaw (shape 4 5 7) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 4 5 7) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_4_6_6 : (initialProbs (shape 4 6 6)).Encloses (initialLaw (shape 4 6 6) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 4 6 6) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_5_5_6 : (initialProbs (shape 5 5 6)).Encloses (initialLaw (shape 5 5 6) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 5 5 6) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_sound (g : Shape) (hg : g ∈ sortedInitial) :
    (initialProbs g).Encloses (initialLaw g : ℝ) := by
  rw [sortedInitial_list] at hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact initialProbs_0_0_16
  · exact initialProbs_0_1_15
  · exact initialProbs_0_2_14
  · exact initialProbs_0_3_13
  · exact initialProbs_0_4_12
  · exact initialProbs_0_5_11
  · exact initialProbs_0_6_10
  · exact initialProbs_0_7_9
  · exact initialProbs_0_8_8
  · exact initialProbs_1_1_14
  · exact initialProbs_1_2_13
  · exact initialProbs_1_3_12
  · exact initialProbs_1_4_11
  · exact initialProbs_1_5_10
  · exact initialProbs_1_6_9
  · exact initialProbs_1_7_8
  · exact initialProbs_2_2_12
  · exact initialProbs_2_3_11
  · exact initialProbs_2_4_10
  · exact initialProbs_2_5_9
  · exact initialProbs_2_6_8
  · exact initialProbs_2_7_7
  · exact initialProbs_3_3_10
  · exact initialProbs_3_4_9
  · exact initialProbs_3_5_8
  · exact initialProbs_3_6_7
  · exact initialProbs_4_4_8
  · exact initialProbs_4_5_7
  · exact initialProbs_4_6_6
  · exact initialProbs_5_5_6

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
lemma w167_sound : w167.Encloses (weight (-5561) : ℝ) := by
  exact weight_enclosed_of_trace (-5561) w167Trace w167S0 w167S1 w167S2 w167S3 w167S4 w167S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

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
lemma w27_sound : w27.Encloses (weight (-55254) : ℝ) := by
  exact weight_enclosed_of_trace (-55254) w27Trace w27S0 w27S1 w27S2 w27S3 w27S4 w27S5
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
open AllFieldInitialEntropyCertificate
open scoped BigOperators
lemma B1_2_5_below : below (shape 1 2 5) = [
  (shape 0 0 4),
  (shape 0 1 3),
  (shape 0 2 2),
  (shape 1 0 3),
  (shape 1 1 2),
  (shape 1 2 1)] := by decide +kernel
lemma B1_2_5Raw_0_0_4 : (B1_2_5Raw (shape 0 0 4)).Encloses (splitWeight positiveSecond tablep (shape 1 2 5) (shape 0 0 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 1 2 5) (shape 0 0 4)
    (0) (-5561) (-55254) w195 w167 w27
    (by decide +kernel) w195_sound w167_sound w27_sound) (by decide +kernel)
lemma B1_2_5Raw_0_1_3 : (B1_2_5Raw (shape 0 1 3)).Encloses (splitWeight positiveSecond tablep (shape 1 2 5) (shape 0 1 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 1 2 5) (shape 0 1 3)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma B1_2_5Raw_0_2_2 : (B1_2_5Raw (shape 0 2 2)).Encloses (splitWeight positiveSecond tablep (shape 1 2 5) (shape 0 2 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 1 2 5) (shape 0 2 2)
    (0) (-5561) (0) w195 w167 w195
    (by decide +kernel) w195_sound w167_sound w195_sound) (by decide +kernel)
lemma B1_2_5Raw_1_0_3 : (B1_2_5Raw (shape 1 0 3)).Encloses (splitWeight positiveSecond tablep (shape 1 2 5) (shape 1 0 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 1 2 5) (shape 1 0 3)
    (0) (-5561) (0) w195 w167 w195
    (by decide +kernel) w195_sound w167_sound w195_sound) (by decide +kernel)
lemma B1_2_5Raw_1_1_2 : (B1_2_5Raw (shape 1 1 2)).Encloses (splitWeight positiveSecond tablep (shape 1 2 5) (shape 1 1 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 1 2 5) (shape 1 1 2)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma B1_2_5Raw_1_2_1 : (B1_2_5Raw (shape 1 2 1)).Encloses (splitWeight positiveSecond tablep (shape 1 2 5) (shape 1 2 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 1 2 5) (shape 1 2 1)
    (0) (-5561) (-55254) w195 w167 w27
    (by decide +kernel) w195_sound w167_sound w27_sound) (by decide +kernel)
lemma B1_2_5Raw_sound (u : Shape) (hu : u ∈ below (shape 1 2 5)) :
    (B1_2_5Raw u).Encloses (splitWeight positiveSecond tablep (shape 1 2 5) u : ℝ) := by
  rw [B1_2_5_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · exact B1_2_5Raw_0_0_4
  · exact B1_2_5Raw_0_1_3
  · exact B1_2_5Raw_0_2_2
  · exact B1_2_5Raw_1_0_3
  · exact B1_2_5Raw_1_1_2
  · exact B1_2_5Raw_1_2_1
lemma B1_2_5Den_sound : B1_2_5Den.Encloses (((below (shape 1 2 5)).map (splitWeight positiveSecond tablep (shape 1 2 5))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (below (shape 1 2 5)) B1_2_5Raw (splitWeight positiveSecond tablep (shape 1 2 5)) B1_2_5Raw_sound) (by decide +kernel)
lemma B1_2_5Den_positive : 0 < B1_2_5Den.lower := by decide +kernel
lemma B1_2_5Law_check_0_0_4 : contains (.mul (B1_2_5Raw (shape 0 0 4)) (.inv B1_2_5Den)) (B1_2_5Table (shape 0 0 4)) = true := by decide +kernel
lemma B1_2_5Law_check_0_1_3 : contains (.mul (B1_2_5Raw (shape 0 1 3)) (.inv B1_2_5Den)) (B1_2_5Table (shape 0 1 3)) = true := by decide +kernel
lemma B1_2_5Law_check_0_2_2 : contains (.mul (B1_2_5Raw (shape 0 2 2)) (.inv B1_2_5Den)) (B1_2_5Table (shape 0 2 2)) = true := by decide +kernel
lemma B1_2_5Law_check_1_0_3 : contains (.mul (B1_2_5Raw (shape 1 0 3)) (.inv B1_2_5Den)) (B1_2_5Table (shape 1 0 3)) = true := by decide +kernel
lemma B1_2_5Law_check_1_1_2 : contains (.mul (B1_2_5Raw (shape 1 1 2)) (.inv B1_2_5Den)) (B1_2_5Table (shape 1 1 2)) = true := by decide +kernel
lemma B1_2_5Law_check_1_2_1 : contains (.mul (B1_2_5Raw (shape 1 2 1)) (.inv B1_2_5Den)) (B1_2_5Table (shape 1 2 1)) = true := by decide +kernel
lemma B1_2_5Law_check (u : Shape) (hu : u ∈ below (shape 1 2 5)) :
    contains (.mul (B1_2_5Raw u) (.inv B1_2_5Den)) (B1_2_5Table u) = true := by
  rw [B1_2_5_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · exact B1_2_5Law_check_0_0_4
  · exact B1_2_5Law_check_0_1_3
  · exact B1_2_5Law_check_0_2_2
  · exact B1_2_5Law_check_1_0_3
  · exact B1_2_5Law_check_1_1_2
  · exact B1_2_5Law_check_1_2_1
lemma B1_2_5Law_sound (u : Shape) :
    (B1_2_5Law u).Encloses (stageBLaw (shape 1 2 5) u : ℝ) := by
  by_cases hu : u ∈ below (shape 1 2 5)
  · have h := contains_sound (Ball.mul_sound (B1_2_5Raw_sound u hu)
      (Ball.inv_sound B1_2_5Den_sound B1_2_5Den_positive)) (B1_2_5Law_check u hu)
    simpa only [B1_2_5Law, hu, ite_true, if_true, stageBLaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [B1_2_5Law, hu, ite_false, if_false, stageBLaw, splitLaw, Rat.cast_zero]
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
lemma second_1_2_5 : (secondProbs (shape 1 2 5)).Encloses (secondMass (shape 1 2 5) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 1 2 5))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 1 2 5))))
  · decide +kernel

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal1_2_5
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
lemma B1_2_5U0_0_4Mass_sound : B1_2_5U0_0_4Mass.Encloses (littleMass (shape 1 2 5) (shape 0 0 4) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_1_2_5))
    (B1_2_5Law_sound (shape 0 0 4))) (by decide +kernel)
lemma B1_2_5U0_1_3Mass_sound : B1_2_5U0_1_3Mass.Encloses (littleMass (shape 1 2 5) (shape 0 1 3) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_1_2_5))
    (B1_2_5Law_sound (shape 0 1 3))) (by decide +kernel)
lemma B1_2_5U0_2_2Mass_sound : B1_2_5U0_2_2Mass.Encloses (littleMass (shape 1 2 5) (shape 0 2 2) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_1_2_5))
    (B1_2_5Law_sound (shape 0 2 2))) (by decide +kernel)
lemma B1_2_5U1_0_3Mass_sound : B1_2_5U1_0_3Mass.Encloses (littleMass (shape 1 2 5) (shape 1 0 3) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_1_2_5))
    (B1_2_5Law_sound (shape 1 0 3))) (by decide +kernel)
lemma B1_2_5U1_1_2Mass_sound : B1_2_5U1_1_2Mass.Encloses (littleMass (shape 1 2 5) (shape 1 1 2) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_1_2_5))
    (B1_2_5Law_sound (shape 1 1 2))) (by decide +kernel)
lemma B1_2_5U1_2_1Mass_sound : B1_2_5U1_2_1Mass.Encloses (littleMass (shape 1 2 5) (shape 1 2 1) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_1_2_5))
    (B1_2_5Law_sound (shape 1 2 1))) (by decide +kernel)
lemma B1_2_5Masses_sound_oai (u : Shape) (hu : u ∈ below (shape 1 2 5)) :
    (B1_2_5Masses u).Encloses ((fun u => (littleMass (shape 1 2 5) u : ℝ)) u) := by
  rw [B1_2_5_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · exact B1_2_5U0_0_4Mass_sound
  · exact B1_2_5U0_1_3Mass_sound
  · exact B1_2_5U0_2_2Mass_sound
  · exact B1_2_5U1_0_3Mass_sound
  · exact B1_2_5U1_1_2Mass_sound
  · exact B1_2_5U1_2_1Mass_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_2_5Masses_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_2_5Masses_sound_oai
