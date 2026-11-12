-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A4_4_8Law_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T05:59:23.514987+00:00
-- url     : https://prove2.me/submissions/b71b10d4-f6eb-4979-8c38-7fe23da6c589

import Mathlib
import Definitions.Def_OAIQ254M003
import Definitions.Def_OAIQ254M005
import Definitions.Def_OAIQ254M006

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
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.shapeValue_relot
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
lemma w55_sound : w55.Encloses (weight (-34294) : ℝ) := by
  exact weight_enclosed_of_trace (-34294) w55Trace w55S0 w55S1 w55S2 w55S3 w55S4 w55S5
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
lemma w175_sound : w175.Encloses (weight (-4357) : ℝ) := by
  exact weight_enclosed_of_trace (-4357) w175Trace w175S0 w175S1 w175S2 w175S3 w175S4 w175S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w176_sound : w176.Encloses (weight (-4343) : ℝ) := by
  exact weight_enclosed_of_trace (-4343) w176Trace w176S0 w176S1 w176S2 w176S3 w176S4 w176S5
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
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitA1_3_12
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
lemma w126_sound : w126.Encloses (weight (-10580) : ℝ) := by
  exact weight_enclosed_of_trace (-10580) w126Trace w126S0 w126S1 w126S2 w126S3 w126S4 w126S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitB2_3_3
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
lemma w98_sound : w98.Encloses (weight (-17266) : ℝ) := by
  exact weight_enclosed_of_trace (-17266) w98Trace w98S0 w98S1 w98S2 w98S3 w98S4 w98S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w99_sound : w99.Encloses (weight (-17106) : ℝ) := by
  exact weight_enclosed_of_trace (-17106) w99Trace w99S0 w99S1 w99S2 w99S3 w99S4 w99S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitB1_3_4
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
lemma w0_sound : w0.Encloses (weight (-120770) : ℝ) := by
  exact weight_enclosed_of_trace (-120770) w0Trace w0S0 w0S1 w0S2 w0S3 w0S4 w0S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w12_sound : w12.Encloses (weight (-70820) : ℝ) := by
  exact weight_enclosed_of_trace (-70820) w12Trace w12S0 w12S1 w12S2 w12S3 w12S4 w12S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

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
open AllFieldInitialEntropyCertificate
open scoped BigOperators
lemma A4_4_8_below : below (shape 4 4 8) = [
  (shape 0 0 8),
  (shape 0 1 7),
  (shape 0 2 6),
  (shape 0 3 5),
  (shape 0 4 4),
  (shape 1 0 7),
  (shape 1 1 6),
  (shape 1 2 5),
  (shape 1 3 4),
  (shape 1 4 3),
  (shape 2 0 6),
  (shape 2 1 5),
  (shape 2 2 4),
  (shape 2 3 3),
  (shape 2 4 2),
  (shape 3 0 5),
  (shape 3 1 4),
  (shape 3 2 3),
  (shape 3 3 2),
  (shape 3 4 1),
  (shape 4 0 4),
  (shape 4 1 3),
  (shape 4 2 2),
  (shape 4 3 1),
  (shape 4 4 0)] := by decide +kernel
lemma A4_4_8Raw_0_0_8 : (A4_4_8Raw (shape 0 0 8)).Encloses (splitWeight positiveInitial tableP (shape 4 4 8) (shape 0 0 8) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 4 8) (shape 0 0 8)
    (-17266) (-17106) (-120770) w98 w99 w0
    (by decide +kernel) w98_sound w99_sound w0_sound) (by decide +kernel)
lemma A4_4_8Raw_0_1_7 : (A4_4_8Raw (shape 0 1 7)).Encloses (splitWeight positiveInitial tableP (shape 4 4 8) (shape 0 1 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 4 8) (shape 0 1 7)
    (-17266) (-4343) (-70820) w98 w176 w12
    (by decide +kernel) w98_sound w176_sound w12_sound) (by decide +kernel)
lemma A4_4_8Raw_0_2_6 : (A4_4_8Raw (shape 0 2 6)).Encloses (splitWeight positiveInitial tableP (shape 4 4 8) (shape 0 2 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 4 8) (shape 0 2 6)
    (-17266) (0) (-34294) w98 w195 w55
    (by decide +kernel) w98_sound w195_sound w55_sound) (by decide +kernel)
lemma A4_4_8Raw_0_3_5 : (A4_4_8Raw (shape 0 3 5)).Encloses (splitWeight positiveInitial tableP (shape 4 4 8) (shape 0 3 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 4 8) (shape 0 3 5)
    (-17266) (-4343) (-10580) w98 w176 w126
    (by decide +kernel) w98_sound w176_sound w126_sound) (by decide +kernel)
lemma A4_4_8Raw_0_4_4 : (A4_4_8Raw (shape 0 4 4)).Encloses (splitWeight positiveInitial tableP (shape 4 4 8) (shape 0 4 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 4 8) (shape 0 4 4)
    (-17266) (-17106) (0) w98 w99 w195
    (by decide +kernel) w98_sound w99_sound w195_sound) (by decide +kernel)
lemma A4_4_8Raw_1_0_7 : (A4_4_8Raw (shape 1 0 7)).Encloses (splitWeight positiveInitial tableP (shape 4 4 8) (shape 1 0 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 4 8) (shape 1 0 7)
    (-4357) (-17106) (-70820) w175 w99 w12
    (by decide +kernel) w175_sound w99_sound w12_sound) (by decide +kernel)
lemma A4_4_8Raw_1_1_6 : (A4_4_8Raw (shape 1 1 6)).Encloses (splitWeight positiveInitial tableP (shape 4 4 8) (shape 1 1 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 4 8) (shape 1 1 6)
    (-4357) (-4343) (-34294) w175 w176 w55
    (by decide +kernel) w175_sound w176_sound w55_sound) (by decide +kernel)
lemma A4_4_8Raw_1_2_5 : (A4_4_8Raw (shape 1 2 5)).Encloses (splitWeight positiveInitial tableP (shape 4 4 8) (shape 1 2 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 4 8) (shape 1 2 5)
    (-4357) (0) (-10580) w175 w195 w126
    (by decide +kernel) w175_sound w195_sound w126_sound) (by decide +kernel)
lemma A4_4_8Raw_1_3_4 : (A4_4_8Raw (shape 1 3 4)).Encloses (splitWeight positiveInitial tableP (shape 4 4 8) (shape 1 3 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 4 8) (shape 1 3 4)
    (-4357) (-4343) (0) w175 w176 w195
    (by decide +kernel) w175_sound w176_sound w195_sound) (by decide +kernel)
lemma A4_4_8Raw_1_4_3 : (A4_4_8Raw (shape 1 4 3)).Encloses (splitWeight positiveInitial tableP (shape 4 4 8) (shape 1 4 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 4 8) (shape 1 4 3)
    (-4357) (-17106) (-10580) w175 w99 w126
    (by decide +kernel) w175_sound w99_sound w126_sound) (by decide +kernel)
lemma A4_4_8Raw_2_0_6 : (A4_4_8Raw (shape 2 0 6)).Encloses (splitWeight positiveInitial tableP (shape 4 4 8) (shape 2 0 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 4 8) (shape 2 0 6)
    (0) (-17106) (-34294) w195 w99 w55
    (by decide +kernel) w195_sound w99_sound w55_sound) (by decide +kernel)
lemma A4_4_8Raw_2_1_5 : (A4_4_8Raw (shape 2 1 5)).Encloses (splitWeight positiveInitial tableP (shape 4 4 8) (shape 2 1 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 4 8) (shape 2 1 5)
    (0) (-4343) (-10580) w195 w176 w126
    (by decide +kernel) w195_sound w176_sound w126_sound) (by decide +kernel)
lemma A4_4_8Raw_2_2_4 : (A4_4_8Raw (shape 2 2 4)).Encloses (splitWeight positiveInitial tableP (shape 4 4 8) (shape 2 2 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 4 8) (shape 2 2 4)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A4_4_8Raw_2_3_3 : (A4_4_8Raw (shape 2 3 3)).Encloses (splitWeight positiveInitial tableP (shape 4 4 8) (shape 2 3 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 4 8) (shape 2 3 3)
    (0) (-4343) (-10580) w195 w176 w126
    (by decide +kernel) w195_sound w176_sound w126_sound) (by decide +kernel)
lemma A4_4_8Raw_2_4_2 : (A4_4_8Raw (shape 2 4 2)).Encloses (splitWeight positiveInitial tableP (shape 4 4 8) (shape 2 4 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 4 8) (shape 2 4 2)
    (0) (-17106) (-34294) w195 w99 w55
    (by decide +kernel) w195_sound w99_sound w55_sound) (by decide +kernel)
lemma A4_4_8Raw_3_0_5 : (A4_4_8Raw (shape 3 0 5)).Encloses (splitWeight positiveInitial tableP (shape 4 4 8) (shape 3 0 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 4 8) (shape 3 0 5)
    (-4357) (-17106) (-10580) w175 w99 w126
    (by decide +kernel) w175_sound w99_sound w126_sound) (by decide +kernel)
lemma A4_4_8Raw_3_1_4 : (A4_4_8Raw (shape 3 1 4)).Encloses (splitWeight positiveInitial tableP (shape 4 4 8) (shape 3 1 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 4 8) (shape 3 1 4)
    (-4357) (-4343) (0) w175 w176 w195
    (by decide +kernel) w175_sound w176_sound w195_sound) (by decide +kernel)
lemma A4_4_8Raw_3_2_3 : (A4_4_8Raw (shape 3 2 3)).Encloses (splitWeight positiveInitial tableP (shape 4 4 8) (shape 3 2 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 4 8) (shape 3 2 3)
    (-4357) (0) (-10580) w175 w195 w126
    (by decide +kernel) w175_sound w195_sound w126_sound) (by decide +kernel)
lemma A4_4_8Raw_3_3_2 : (A4_4_8Raw (shape 3 3 2)).Encloses (splitWeight positiveInitial tableP (shape 4 4 8) (shape 3 3 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 4 8) (shape 3 3 2)
    (-4357) (-4343) (-34294) w175 w176 w55
    (by decide +kernel) w175_sound w176_sound w55_sound) (by decide +kernel)
lemma A4_4_8Raw_3_4_1 : (A4_4_8Raw (shape 3 4 1)).Encloses (splitWeight positiveInitial tableP (shape 4 4 8) (shape 3 4 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 4 8) (shape 3 4 1)
    (-4357) (-17106) (-70820) w175 w99 w12
    (by decide +kernel) w175_sound w99_sound w12_sound) (by decide +kernel)
lemma A4_4_8Raw_4_0_4 : (A4_4_8Raw (shape 4 0 4)).Encloses (splitWeight positiveInitial tableP (shape 4 4 8) (shape 4 0 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 4 8) (shape 4 0 4)
    (-17266) (-17106) (0) w98 w99 w195
    (by decide +kernel) w98_sound w99_sound w195_sound) (by decide +kernel)
lemma A4_4_8Raw_4_1_3 : (A4_4_8Raw (shape 4 1 3)).Encloses (splitWeight positiveInitial tableP (shape 4 4 8) (shape 4 1 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 4 8) (shape 4 1 3)
    (-17266) (-4343) (-10580) w98 w176 w126
    (by decide +kernel) w98_sound w176_sound w126_sound) (by decide +kernel)
lemma A4_4_8Raw_4_2_2 : (A4_4_8Raw (shape 4 2 2)).Encloses (splitWeight positiveInitial tableP (shape 4 4 8) (shape 4 2 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 4 8) (shape 4 2 2)
    (-17266) (0) (-34294) w98 w195 w55
    (by decide +kernel) w98_sound w195_sound w55_sound) (by decide +kernel)
lemma A4_4_8Raw_4_3_1 : (A4_4_8Raw (shape 4 3 1)).Encloses (splitWeight positiveInitial tableP (shape 4 4 8) (shape 4 3 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 4 8) (shape 4 3 1)
    (-17266) (-4343) (-70820) w98 w176 w12
    (by decide +kernel) w98_sound w176_sound w12_sound) (by decide +kernel)
lemma A4_4_8Raw_4_4_0 : (A4_4_8Raw (shape 4 4 0)).Encloses (splitWeight positiveInitial tableP (shape 4 4 8) (shape 4 4 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 4 8) (shape 4 4 0)
    (-17266) (-17106) (-120770) w98 w99 w0
    (by decide +kernel) w98_sound w99_sound w0_sound) (by decide +kernel)
lemma A4_4_8Raw_sound (u : Shape) (hu : u ∈ below (shape 4 4 8)) :
    (A4_4_8Raw u).Encloses (splitWeight positiveInitial tableP (shape 4 4 8) u : ℝ) := by
  rw [A4_4_8_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A4_4_8Raw_0_0_8
  · exact A4_4_8Raw_0_1_7
  · exact A4_4_8Raw_0_2_6
  · exact A4_4_8Raw_0_3_5
  · exact A4_4_8Raw_0_4_4
  · exact A4_4_8Raw_1_0_7
  · exact A4_4_8Raw_1_1_6
  · exact A4_4_8Raw_1_2_5
  · exact A4_4_8Raw_1_3_4
  · exact A4_4_8Raw_1_4_3
  · exact A4_4_8Raw_2_0_6
  · exact A4_4_8Raw_2_1_5
  · exact A4_4_8Raw_2_2_4
  · exact A4_4_8Raw_2_3_3
  · exact A4_4_8Raw_2_4_2
  · exact A4_4_8Raw_3_0_5
  · exact A4_4_8Raw_3_1_4
  · exact A4_4_8Raw_3_2_3
  · exact A4_4_8Raw_3_3_2
  · exact A4_4_8Raw_3_4_1
  · exact A4_4_8Raw_4_0_4
  · exact A4_4_8Raw_4_1_3
  · exact A4_4_8Raw_4_2_2
  · exact A4_4_8Raw_4_3_1
  · exact A4_4_8Raw_4_4_0
lemma A4_4_8Den_sound : A4_4_8Den.Encloses (((below (shape 4 4 8)).map (splitWeight positiveInitial tableP (shape 4 4 8))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (below (shape 4 4 8)) A4_4_8Raw (splitWeight positiveInitial tableP (shape 4 4 8)) A4_4_8Raw_sound) (by decide +kernel)
lemma A4_4_8Den_positive : 0 < A4_4_8Den.lower := by decide +kernel
lemma A4_4_8Law_check_0_0_8 : contains (.mul (A4_4_8Raw (shape 0 0 8)) (.inv A4_4_8Den)) (A4_4_8Table (shape 0 0 8)) = true := by decide +kernel
lemma A4_4_8Law_check_0_1_7 : contains (.mul (A4_4_8Raw (shape 0 1 7)) (.inv A4_4_8Den)) (A4_4_8Table (shape 0 1 7)) = true := by decide +kernel
lemma A4_4_8Law_check_0_2_6 : contains (.mul (A4_4_8Raw (shape 0 2 6)) (.inv A4_4_8Den)) (A4_4_8Table (shape 0 2 6)) = true := by decide +kernel
lemma A4_4_8Law_check_0_3_5 : contains (.mul (A4_4_8Raw (shape 0 3 5)) (.inv A4_4_8Den)) (A4_4_8Table (shape 0 3 5)) = true := by decide +kernel
lemma A4_4_8Law_check_0_4_4 : contains (.mul (A4_4_8Raw (shape 0 4 4)) (.inv A4_4_8Den)) (A4_4_8Table (shape 0 4 4)) = true := by decide +kernel
lemma A4_4_8Law_check_1_0_7 : contains (.mul (A4_4_8Raw (shape 1 0 7)) (.inv A4_4_8Den)) (A4_4_8Table (shape 1 0 7)) = true := by decide +kernel
lemma A4_4_8Law_check_1_1_6 : contains (.mul (A4_4_8Raw (shape 1 1 6)) (.inv A4_4_8Den)) (A4_4_8Table (shape 1 1 6)) = true := by decide +kernel
lemma A4_4_8Law_check_1_2_5 : contains (.mul (A4_4_8Raw (shape 1 2 5)) (.inv A4_4_8Den)) (A4_4_8Table (shape 1 2 5)) = true := by decide +kernel
lemma A4_4_8Law_check_1_3_4 : contains (.mul (A4_4_8Raw (shape 1 3 4)) (.inv A4_4_8Den)) (A4_4_8Table (shape 1 3 4)) = true := by decide +kernel
lemma A4_4_8Law_check_1_4_3 : contains (.mul (A4_4_8Raw (shape 1 4 3)) (.inv A4_4_8Den)) (A4_4_8Table (shape 1 4 3)) = true := by decide +kernel
lemma A4_4_8Law_check_2_0_6 : contains (.mul (A4_4_8Raw (shape 2 0 6)) (.inv A4_4_8Den)) (A4_4_8Table (shape 2 0 6)) = true := by decide +kernel
lemma A4_4_8Law_check_2_1_5 : contains (.mul (A4_4_8Raw (shape 2 1 5)) (.inv A4_4_8Den)) (A4_4_8Table (shape 2 1 5)) = true := by decide +kernel
lemma A4_4_8Law_check_2_2_4 : contains (.mul (A4_4_8Raw (shape 2 2 4)) (.inv A4_4_8Den)) (A4_4_8Table (shape 2 2 4)) = true := by decide +kernel
lemma A4_4_8Law_check_2_3_3 : contains (.mul (A4_4_8Raw (shape 2 3 3)) (.inv A4_4_8Den)) (A4_4_8Table (shape 2 3 3)) = true := by decide +kernel
lemma A4_4_8Law_check_2_4_2 : contains (.mul (A4_4_8Raw (shape 2 4 2)) (.inv A4_4_8Den)) (A4_4_8Table (shape 2 4 2)) = true := by decide +kernel
lemma A4_4_8Law_check_3_0_5 : contains (.mul (A4_4_8Raw (shape 3 0 5)) (.inv A4_4_8Den)) (A4_4_8Table (shape 3 0 5)) = true := by decide +kernel
lemma A4_4_8Law_check_3_1_4 : contains (.mul (A4_4_8Raw (shape 3 1 4)) (.inv A4_4_8Den)) (A4_4_8Table (shape 3 1 4)) = true := by decide +kernel
lemma A4_4_8Law_check_3_2_3 : contains (.mul (A4_4_8Raw (shape 3 2 3)) (.inv A4_4_8Den)) (A4_4_8Table (shape 3 2 3)) = true := by decide +kernel
lemma A4_4_8Law_check_3_3_2 : contains (.mul (A4_4_8Raw (shape 3 3 2)) (.inv A4_4_8Den)) (A4_4_8Table (shape 3 3 2)) = true := by decide +kernel
lemma A4_4_8Law_check_3_4_1 : contains (.mul (A4_4_8Raw (shape 3 4 1)) (.inv A4_4_8Den)) (A4_4_8Table (shape 3 4 1)) = true := by decide +kernel
lemma A4_4_8Law_check_4_0_4 : contains (.mul (A4_4_8Raw (shape 4 0 4)) (.inv A4_4_8Den)) (A4_4_8Table (shape 4 0 4)) = true := by decide +kernel
lemma A4_4_8Law_check_4_1_3 : contains (.mul (A4_4_8Raw (shape 4 1 3)) (.inv A4_4_8Den)) (A4_4_8Table (shape 4 1 3)) = true := by decide +kernel
lemma A4_4_8Law_check_4_2_2 : contains (.mul (A4_4_8Raw (shape 4 2 2)) (.inv A4_4_8Den)) (A4_4_8Table (shape 4 2 2)) = true := by decide +kernel
lemma A4_4_8Law_check_4_3_1 : contains (.mul (A4_4_8Raw (shape 4 3 1)) (.inv A4_4_8Den)) (A4_4_8Table (shape 4 3 1)) = true := by decide +kernel
lemma A4_4_8Law_check_4_4_0 : contains (.mul (A4_4_8Raw (shape 4 4 0)) (.inv A4_4_8Den)) (A4_4_8Table (shape 4 4 0)) = true := by decide +kernel
lemma A4_4_8Law_check (u : Shape) (hu : u ∈ below (shape 4 4 8)) :
    contains (.mul (A4_4_8Raw u) (.inv A4_4_8Den)) (A4_4_8Table u) = true := by
  rw [A4_4_8_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A4_4_8Law_check_0_0_8
  · exact A4_4_8Law_check_0_1_7
  · exact A4_4_8Law_check_0_2_6
  · exact A4_4_8Law_check_0_3_5
  · exact A4_4_8Law_check_0_4_4
  · exact A4_4_8Law_check_1_0_7
  · exact A4_4_8Law_check_1_1_6
  · exact A4_4_8Law_check_1_2_5
  · exact A4_4_8Law_check_1_3_4
  · exact A4_4_8Law_check_1_4_3
  · exact A4_4_8Law_check_2_0_6
  · exact A4_4_8Law_check_2_1_5
  · exact A4_4_8Law_check_2_2_4
  · exact A4_4_8Law_check_2_3_3
  · exact A4_4_8Law_check_2_4_2
  · exact A4_4_8Law_check_3_0_5
  · exact A4_4_8Law_check_3_1_4
  · exact A4_4_8Law_check_3_2_3
  · exact A4_4_8Law_check_3_3_2
  · exact A4_4_8Law_check_3_4_1
  · exact A4_4_8Law_check_4_0_4
  · exact A4_4_8Law_check_4_1_3
  · exact A4_4_8Law_check_4_2_2
  · exact A4_4_8Law_check_4_3_1
  · exact A4_4_8Law_check_4_4_0
lemma A4_4_8Law_sound_oai (u : Shape) :
    (A4_4_8Law u).Encloses (stageALaw (shape 4 4 8) u : ℝ) := by
  by_cases hu : u ∈ below (shape 4 4 8)
  · have h := contains_sound (Ball.mul_sound (A4_4_8Raw_sound u hu)
      (Ball.inv_sound A4_4_8Den_sound A4_4_8Den_positive)) (A4_4_8Law_check u hu)
    simpa only [A4_4_8Law, hu, ite_true, if_true, stageALaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [A4_4_8Law, hu, ite_false, if_false, stageALaw, splitLaw, Rat.cast_zero]
    simpa only [Rat.cast_zero] using Ball.exact_sound 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A4_4_8Law_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A4_4_8Law_sound_oai
