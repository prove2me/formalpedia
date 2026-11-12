-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.nativeLBBall_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:16:28.665242+00:00
-- url     : https://prove2.me/submissions/93d6cc8a-8cc9-4efc-9ab4-7c1528ff9ffe

import Mathlib
import Definitions.Def_OAIQ254M011
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_AProbsTable_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_capacityBBalls_sound

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
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators

lemma forall_fin3 {P : Fin 3 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) : ∀ i, P i := by
  intro i
  fin_cases i <;> assumption

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
lemma allSecond_list : shapes 8 = [
  (shape 0 0 8),
  (shape 0 1 7),
  (shape 0 2 6),
  (shape 0 3 5),
  (shape 0 4 4),
  (shape 0 5 3),
  (shape 0 6 2),
  (shape 0 7 1),
  (shape 0 8 0),
  (shape 1 0 7),
  (shape 1 1 6),
  (shape 1 2 5),
  (shape 1 3 4),
  (shape 1 4 3),
  (shape 1 5 2),
  (shape 1 6 1),
  (shape 1 7 0),
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
  (shape 3 5 0),
  (shape 4 0 4),
  (shape 4 1 3),
  (shape 4 2 2),
  (shape 4 3 1),
  (shape 4 4 0),
  (shape 5 0 3),
  (shape 5 1 2),
  (shape 5 2 1),
  (shape 5 3 0),
  (shape 6 0 2),
  (shape 6 1 1),
  (shape 6 2 0),
  (shape 7 0 1),
  (shape 7 1 0),
  (shape 8 0 0)] := by decide +kernel

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
lemma second_0_0_8 : (secondProbs (shape 0 0 8)).Encloses (secondMass (shape 0 0 8) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 0 0 8))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 0 0 8))))
  · decide +kernel
lemma second_0_1_7 : (secondProbs (shape 0 1 7)).Encloses (secondMass (shape 0 1 7) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 0 1 7))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 0 1 7))))
  · decide +kernel
lemma second_0_2_6 : (secondProbs (shape 0 2 6)).Encloses (secondMass (shape 0 2 6) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 0 2 6))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 0 2 6))))
  · decide +kernel
lemma second_0_3_5 : (secondProbs (shape 0 3 5)).Encloses (secondMass (shape 0 3 5) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 0 3 5))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 0 3 5))))
  · decide +kernel
lemma second_0_4_4 : (secondProbs (shape 0 4 4)).Encloses (secondMass (shape 0 4 4) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 0 4 4))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 0 4 4))))
  · decide +kernel
lemma second_0_5_3 : (secondProbs (shape 0 5 3)).Encloses (secondMass (shape 0 5 3) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 0 5 3))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 0 5 3))))
  · decide +kernel
lemma second_0_6_2 : (secondProbs (shape 0 6 2)).Encloses (secondMass (shape 0 6 2) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 0 6 2))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 0 6 2))))
  · decide +kernel
lemma second_0_7_1 : (secondProbs (shape 0 7 1)).Encloses (secondMass (shape 0 7 1) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 0 7 1))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 0 7 1))))
  · decide +kernel
lemma second_0_8_0 : (secondProbs (shape 0 8 0)).Encloses (secondMass (shape 0 8 0) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 0 8 0))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 0 8 0))))
  · decide +kernel
lemma second_1_0_7 : (secondProbs (shape 1 0 7)).Encloses (secondMass (shape 1 0 7) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 1 0 7))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 1 0 7))))
  · decide +kernel
lemma second_1_1_6 : (secondProbs (shape 1 1 6)).Encloses (secondMass (shape 1 1 6) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 1 1 6))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 1 1 6))))
  · decide +kernel
lemma second_1_2_5 : (secondProbs (shape 1 2 5)).Encloses (secondMass (shape 1 2 5) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 1 2 5))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 1 2 5))))
  · decide +kernel
lemma second_1_3_4 : (secondProbs (shape 1 3 4)).Encloses (secondMass (shape 1 3 4) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 1 3 4))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 1 3 4))))
  · decide +kernel
lemma second_1_4_3 : (secondProbs (shape 1 4 3)).Encloses (secondMass (shape 1 4 3) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 1 4 3))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 1 4 3))))
  · decide +kernel
lemma second_1_5_2 : (secondProbs (shape 1 5 2)).Encloses (secondMass (shape 1 5 2) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 1 5 2))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 1 5 2))))
  · decide +kernel
lemma second_1_6_1 : (secondProbs (shape 1 6 1)).Encloses (secondMass (shape 1 6 1) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 1 6 1))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 1 6 1))))
  · decide +kernel
lemma second_1_7_0 : (secondProbs (shape 1 7 0)).Encloses (secondMass (shape 1 7 0) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 1 7 0))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 1 7 0))))
  · decide +kernel
lemma second_2_0_6 : (secondProbs (shape 2 0 6)).Encloses (secondMass (shape 2 0 6) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 2 0 6))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 2 0 6))))
  · decide +kernel
lemma second_2_1_5 : (secondProbs (shape 2 1 5)).Encloses (secondMass (shape 2 1 5) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 2 1 5))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 2 1 5))))
  · decide +kernel
lemma second_2_2_4 : (secondProbs (shape 2 2 4)).Encloses (secondMass (shape 2 2 4) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 2 2 4))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 2 2 4))))
  · decide +kernel
lemma second_2_3_3 : (secondProbs (shape 2 3 3)).Encloses (secondMass (shape 2 3 3) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 2 3 3))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 2 3 3))))
  · decide +kernel
lemma second_2_4_2 : (secondProbs (shape 2 4 2)).Encloses (secondMass (shape 2 4 2) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 2 4 2))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 2 4 2))))
  · decide +kernel
lemma second_2_5_1 : (secondProbs (shape 2 5 1)).Encloses (secondMass (shape 2 5 1) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 2 5 1))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 2 5 1))))
  · decide +kernel
lemma second_2_6_0 : (secondProbs (shape 2 6 0)).Encloses (secondMass (shape 2 6 0) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 2 6 0))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 2 6 0))))
  · decide +kernel
lemma second_3_0_5 : (secondProbs (shape 3 0 5)).Encloses (secondMass (shape 3 0 5) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 3 0 5))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 3 0 5))))
  · decide +kernel
lemma second_3_1_4 : (secondProbs (shape 3 1 4)).Encloses (secondMass (shape 3 1 4) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 3 1 4))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 3 1 4))))
  · decide +kernel
lemma second_3_2_3 : (secondProbs (shape 3 2 3)).Encloses (secondMass (shape 3 2 3) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 3 2 3))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 3 2 3))))
  · decide +kernel
lemma second_3_3_2 : (secondProbs (shape 3 3 2)).Encloses (secondMass (shape 3 3 2) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 3 3 2))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 3 3 2))))
  · decide +kernel
lemma second_3_4_1 : (secondProbs (shape 3 4 1)).Encloses (secondMass (shape 3 4 1) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 3 4 1))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 3 4 1))))
  · decide +kernel
lemma second_3_5_0 : (secondProbs (shape 3 5 0)).Encloses (secondMass (shape 3 5 0) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 3 5 0))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 3 5 0))))
  · decide +kernel
lemma second_4_0_4 : (secondProbs (shape 4 0 4)).Encloses (secondMass (shape 4 0 4) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 4 0 4))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 4 0 4))))
  · decide +kernel
lemma second_4_1_3 : (secondProbs (shape 4 1 3)).Encloses (secondMass (shape 4 1 3) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 4 1 3))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 4 1 3))))
  · decide +kernel
lemma second_4_2_2 : (secondProbs (shape 4 2 2)).Encloses (secondMass (shape 4 2 2) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 4 2 2))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 4 2 2))))
  · decide +kernel
lemma second_4_3_1 : (secondProbs (shape 4 3 1)).Encloses (secondMass (shape 4 3 1) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 4 3 1))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 4 3 1))))
  · decide +kernel
lemma second_4_4_0 : (secondProbs (shape 4 4 0)).Encloses (secondMass (shape 4 4 0) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 4 4 0))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 4 4 0))))
  · decide +kernel
lemma second_5_0_3 : (secondProbs (shape 5 0 3)).Encloses (secondMass (shape 5 0 3) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 5 0 3))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 5 0 3))))
  · decide +kernel
lemma second_5_1_2 : (secondProbs (shape 5 1 2)).Encloses (secondMass (shape 5 1 2) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 5 1 2))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 5 1 2))))
  · decide +kernel
lemma second_5_2_1 : (secondProbs (shape 5 2 1)).Encloses (secondMass (shape 5 2 1) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 5 2 1))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 5 2 1))))
  · decide +kernel
lemma second_5_3_0 : (secondProbs (shape 5 3 0)).Encloses (secondMass (shape 5 3 0) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 5 3 0))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 5 3 0))))
  · decide +kernel
lemma second_6_0_2 : (secondProbs (shape 6 0 2)).Encloses (secondMass (shape 6 0 2) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 6 0 2))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 6 0 2))))
  · decide +kernel
lemma second_6_1_1 : (secondProbs (shape 6 1 1)).Encloses (secondMass (shape 6 1 1) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 6 1 1))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 6 1 1))))
  · decide +kernel
lemma second_6_2_0 : (secondProbs (shape 6 2 0)).Encloses (secondMass (shape 6 2 0) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 6 2 0))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 6 2 0))))
  · decide +kernel
lemma second_7_0_1 : (secondProbs (shape 7 0 1)).Encloses (secondMass (shape 7 0 1) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 7 0 1))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 7 0 1))))
  · decide +kernel
lemma second_7_1_0 : (secondProbs (shape 7 1 0)).Encloses (secondMass (shape 7 1 0) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 7 1 0))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 7 1 0))))
  · decide +kernel
lemma second_8_0_0 : (secondProbs (shape 8 0 0)).Encloses (secondMass (shape 8 0 0) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 8 0 0))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 8 0 0))))
  · decide +kernel
lemma secondProbs_sound (t : Shape) (ht : t ∈ shapes 8) :
    (secondProbs t).Encloses (secondMass t : ℝ) := by
  rw [allSecond_list] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact second_0_0_8
  · exact second_0_1_7
  · exact second_0_2_6
  · exact second_0_3_5
  · exact second_0_4_4
  · exact second_0_5_3
  · exact second_0_6_2
  · exact second_0_7_1
  · exact second_0_8_0
  · exact second_1_0_7
  · exact second_1_1_6
  · exact second_1_2_5
  · exact second_1_3_4
  · exact second_1_4_3
  · exact second_1_5_2
  · exact second_1_6_1
  · exact second_1_7_0
  · exact second_2_0_6
  · exact second_2_1_5
  · exact second_2_2_4
  · exact second_2_3_3
  · exact second_2_4_2
  · exact second_2_5_1
  · exact second_2_6_0
  · exact second_3_0_5
  · exact second_3_1_4
  · exact second_3_2_3
  · exact second_3_3_2
  · exact second_3_4_1
  · exact second_3_5_0
  · exact second_4_0_4
  · exact second_4_1_3
  · exact second_4_2_2
  · exact second_4_3_1
  · exact second_4_4_0
  · exact second_5_0_3
  · exact second_5_1_2
  · exact second_5_2_1
  · exact second_5_3_0
  · exact second_6_0_2
  · exact second_6_1_1
  · exact second_6_2_0
  · exact second_7_0_1
  · exact second_7_1_0
  · exact second_8_0_0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_NativeSharp
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
lemma nativeLBBall_sound_0 : (nativeLBBall 0).Encloses (nativeLB 0) := by
  exact contains_sound (listSumBall_sound positiveSecond
    (fun s => .mul (secondProbs s) (capacityBBalls s 0)) _
    (fun s hs => Ball.mul_sound (secondProbs_sound s (List.mem_filter.mp hs).1)
      (capacityBBalls_sound s hs 0))) (by decide +kernel)
lemma nativeLBBall_sound_1 : (nativeLBBall 1).Encloses (nativeLB 1) := by
  exact contains_sound (listSumBall_sound positiveSecond
    (fun s => .mul (secondProbs s) (capacityBBalls s 1)) _
    (fun s hs => Ball.mul_sound (secondProbs_sound s (List.mem_filter.mp hs).1)
      (capacityBBalls_sound s hs 1))) (by decide +kernel)
lemma nativeLBBall_sound_2 : (nativeLBBall 2).Encloses (nativeLB 2) := by
  exact contains_sound (listSumBall_sound positiveSecond
    (fun s => .mul (secondProbs s) (capacityBBalls s 2)) _
    (fun s hs => Ball.mul_sound (secondProbs_sound s (List.mem_filter.mp hs).1)
      (capacityBBalls_sound s hs 2))) (by decide +kernel)
lemma nativeLBBall_sound_oai (i : Fin 3) : (nativeLBBall i).Encloses (nativeLB i) := by
  revert i
  exact forall_fin3 nativeLBBall_sound_0 nativeLBBall_sound_1 nativeLBBall_sound_2

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.nativeLBBall_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.nativeLBBall_sound_oai
