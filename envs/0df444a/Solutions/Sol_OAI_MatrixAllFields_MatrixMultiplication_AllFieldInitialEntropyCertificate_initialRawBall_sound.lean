-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropyCertificate.initialRawBall_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T05:54:25.321563+00:00
-- url     : https://prove2.me/submissions/7e503bcb-c4b6-498f-a9d8-d3ff3e549f75

import Mathlib
import Definitions.Def_OAIQ254M003
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_weight_enclosed_10
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_weight_enclosed_11

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

lemma initial_shape_bound : ∀ s ∈ sortedInitial, ∀ i : Fin 3, s i < 17 := by
  decide +kernel

lemma initialRawBall_sound_oai (s : Shape) (hs : s ∈ sortedInitial) :
    (initialRawBall s).Encloses (initialWeight s : ℝ) := by
  have h := Ball.mul_sound (Ball.exact_sound (initialMultiplicity s : ℚ))
    (Ball.mul_sound (sourceWeightBall_sound (s 0) (initial_shape_bound s hs 0))
      (Ball.mul_sound (sourceWeightBall_sound (s 1) (initial_shape_bound s hs 1))
        (sourceWeightBall_sound (s 2) (initial_shape_bound s hs 2))))
  simpa only [initialRawBall, initialWeight, Rat.cast_mul, Rat.cast_prod,
    Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two] using h

end MatrixMultiplication.AllFieldInitialEntropyCertificate

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropyCertificate.initialRawBall_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropyCertificate.initialRawBall_sound_oai
