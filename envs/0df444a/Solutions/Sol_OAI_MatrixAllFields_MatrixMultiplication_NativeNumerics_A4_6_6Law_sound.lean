-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A4_6_6Law_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T05:59:25.770661+00:00
-- url     : https://prove2.me/submissions/966c9fd2-242a-4508-a794-fa99e99bcdbb

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
lemma w166_sound : w166.Encloses (weight (-5564) : ℝ) := by
  exact weight_enclosed_of_trace (-5564) w166Trace w166S0 w166S1 w166S2 w166S3 w166S4 w166S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w167_sound : w167.Encloses (weight (-5561) : ℝ) := by
  exact weight_enclosed_of_trace (-5561) w167Trace w167S0 w167S1 w167S2 w167S3 w167S4 w167S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w174_sound : w174.Encloses (weight (-4371) : ℝ) := by
  exact weight_enclosed_of_trace (-4371) w174Trace w174S0 w174S1 w174S2 w174S3 w174S4 w174S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Four0_4_4
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
lemma w100_sound : w100.Encloses (weight (-17098) : ℝ) := by
  exact weight_enclosed_of_trace (-17098) w100Trace w100S0 w100S1 w100S2 w100S3 w100S4 w100S5
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
lemma w25_sound : w25.Encloses (weight (-56356) : ℝ) := by
  exact weight_enclosed_of_trace (-56356) w25Trace w25S0 w25S1 w25S2 w25S3 w25S4 w25S5
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
lemma w78_sound : w78.Encloses (weight (-25990) : ℝ) := by
  exact weight_enclosed_of_trace (-25990) w78Trace w78S0 w78S1 w78S2 w78S3 w78S4 w78S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w79_sound : w79.Encloses (weight (-25900) : ℝ) := by
  exact weight_enclosed_of_trace (-25900) w79Trace w79S0 w79S1 w79S2 w79S3 w79S4 w79S5
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
lemma w24_sound : w24.Encloses (weight (-56609) : ℝ) := by
  exact weight_enclosed_of_trace (-56609) w24Trace w24S0 w24S1 w24S2 w24S3 w24S4 w24S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitA4_6_6
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
lemma A4_6_6_below : below (shape 4 6 6) = [
  (shape 0 2 6),
  (shape 0 3 5),
  (shape 0 4 4),
  (shape 0 5 3),
  (shape 0 6 2),
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
  (shape 3 5 0),
  (shape 4 0 4),
  (shape 4 1 3),
  (shape 4 2 2),
  (shape 4 3 1),
  (shape 4 4 0)] := by decide +kernel
lemma A4_6_6Raw_0_2_6 : (A4_6_6Raw (shape 0 2 6)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 0 2 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 0 2 6)
    (-17098) (-5564) (-56356) w100 w166 w25
    (by decide +kernel) w100_sound w166_sound w25_sound) (by decide +kernel)
lemma A4_6_6Raw_0_3_5 : (A4_6_6Raw (shape 0 3 5)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 0 3 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 0 3 5)
    (-17098) (0) (-25900) w100 w195 w79
    (by decide +kernel) w100_sound w195_sound w79_sound) (by decide +kernel)
lemma A4_6_6Raw_0_4_4 : (A4_6_6Raw (shape 0 4 4)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 0 4 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 0 4 4)
    (-17098) (-5564) (-5561) w100 w166 w167
    (by decide +kernel) w100_sound w166_sound w167_sound) (by decide +kernel)
lemma A4_6_6Raw_0_5_3 : (A4_6_6Raw (shape 0 5 3)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 0 5 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 0 5 3)
    (-17098) (-25990) (0) w100 w78 w195
    (by decide +kernel) w100_sound w78_sound w195_sound) (by decide +kernel)
lemma A4_6_6Raw_0_6_2 : (A4_6_6Raw (shape 0 6 2)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 0 6 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 0 6 2)
    (-17098) (-56609) (-5561) w100 w24 w167
    (by decide +kernel) w100_sound w24_sound w167_sound) (by decide +kernel)
lemma A4_6_6Raw_1_1_6 : (A4_6_6Raw (shape 1 1 6)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 1 1 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 1 1 6)
    (-4371) (-25990) (-56356) w174 w78 w25
    (by decide +kernel) w174_sound w78_sound w25_sound) (by decide +kernel)
lemma A4_6_6Raw_1_2_5 : (A4_6_6Raw (shape 1 2 5)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 1 2 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 1 2 5)
    (-4371) (-5564) (-25900) w174 w166 w79
    (by decide +kernel) w174_sound w166_sound w79_sound) (by decide +kernel)
lemma A4_6_6Raw_1_3_4 : (A4_6_6Raw (shape 1 3 4)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 1 3 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 1 3 4)
    (-4371) (0) (-5561) w174 w195 w167
    (by decide +kernel) w174_sound w195_sound w167_sound) (by decide +kernel)
lemma A4_6_6Raw_1_4_3 : (A4_6_6Raw (shape 1 4 3)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 1 4 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 1 4 3)
    (-4371) (-5564) (0) w174 w166 w195
    (by decide +kernel) w174_sound w166_sound w195_sound) (by decide +kernel)
lemma A4_6_6Raw_1_5_2 : (A4_6_6Raw (shape 1 5 2)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 1 5 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 1 5 2)
    (-4371) (-25990) (-5561) w174 w78 w167
    (by decide +kernel) w174_sound w78_sound w167_sound) (by decide +kernel)
lemma A4_6_6Raw_1_6_1 : (A4_6_6Raw (shape 1 6 1)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 1 6 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 1 6 1)
    (-4371) (-56609) (-25900) w174 w24 w79
    (by decide +kernel) w174_sound w24_sound w79_sound) (by decide +kernel)
lemma A4_6_6Raw_2_0_6 : (A4_6_6Raw (shape 2 0 6)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 2 0 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 2 0 6)
    (0) (-56609) (-56356) w195 w24 w25
    (by decide +kernel) w195_sound w24_sound w25_sound) (by decide +kernel)
lemma A4_6_6Raw_2_1_5 : (A4_6_6Raw (shape 2 1 5)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 2 1 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 2 1 5)
    (0) (-25990) (-25900) w195 w78 w79
    (by decide +kernel) w195_sound w78_sound w79_sound) (by decide +kernel)
lemma A4_6_6Raw_2_2_4 : (A4_6_6Raw (shape 2 2 4)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 2 2 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 2 2 4)
    (0) (-5564) (-5561) w195 w166 w167
    (by decide +kernel) w195_sound w166_sound w167_sound) (by decide +kernel)
lemma A4_6_6Raw_2_3_3 : (A4_6_6Raw (shape 2 3 3)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 2 3 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 2 3 3)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A4_6_6Raw_2_4_2 : (A4_6_6Raw (shape 2 4 2)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 2 4 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 2 4 2)
    (0) (-5564) (-5561) w195 w166 w167
    (by decide +kernel) w195_sound w166_sound w167_sound) (by decide +kernel)
lemma A4_6_6Raw_2_5_1 : (A4_6_6Raw (shape 2 5 1)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 2 5 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 2 5 1)
    (0) (-25990) (-25900) w195 w78 w79
    (by decide +kernel) w195_sound w78_sound w79_sound) (by decide +kernel)
lemma A4_6_6Raw_2_6_0 : (A4_6_6Raw (shape 2 6 0)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 2 6 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 2 6 0)
    (0) (-56609) (-56356) w195 w24 w25
    (by decide +kernel) w195_sound w24_sound w25_sound) (by decide +kernel)
lemma A4_6_6Raw_3_0_5 : (A4_6_6Raw (shape 3 0 5)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 3 0 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 3 0 5)
    (-4371) (-56609) (-25900) w174 w24 w79
    (by decide +kernel) w174_sound w24_sound w79_sound) (by decide +kernel)
lemma A4_6_6Raw_3_1_4 : (A4_6_6Raw (shape 3 1 4)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 3 1 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 3 1 4)
    (-4371) (-25990) (-5561) w174 w78 w167
    (by decide +kernel) w174_sound w78_sound w167_sound) (by decide +kernel)
lemma A4_6_6Raw_3_2_3 : (A4_6_6Raw (shape 3 2 3)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 3 2 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 3 2 3)
    (-4371) (-5564) (0) w174 w166 w195
    (by decide +kernel) w174_sound w166_sound w195_sound) (by decide +kernel)
lemma A4_6_6Raw_3_3_2 : (A4_6_6Raw (shape 3 3 2)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 3 3 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 3 3 2)
    (-4371) (0) (-5561) w174 w195 w167
    (by decide +kernel) w174_sound w195_sound w167_sound) (by decide +kernel)
lemma A4_6_6Raw_3_4_1 : (A4_6_6Raw (shape 3 4 1)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 3 4 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 3 4 1)
    (-4371) (-5564) (-25900) w174 w166 w79
    (by decide +kernel) w174_sound w166_sound w79_sound) (by decide +kernel)
lemma A4_6_6Raw_3_5_0 : (A4_6_6Raw (shape 3 5 0)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 3 5 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 3 5 0)
    (-4371) (-25990) (-56356) w174 w78 w25
    (by decide +kernel) w174_sound w78_sound w25_sound) (by decide +kernel)
lemma A4_6_6Raw_4_0_4 : (A4_6_6Raw (shape 4 0 4)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 4 0 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 4 0 4)
    (-17098) (-56609) (-5561) w100 w24 w167
    (by decide +kernel) w100_sound w24_sound w167_sound) (by decide +kernel)
lemma A4_6_6Raw_4_1_3 : (A4_6_6Raw (shape 4 1 3)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 4 1 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 4 1 3)
    (-17098) (-25990) (0) w100 w78 w195
    (by decide +kernel) w100_sound w78_sound w195_sound) (by decide +kernel)
lemma A4_6_6Raw_4_2_2 : (A4_6_6Raw (shape 4 2 2)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 4 2 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 4 2 2)
    (-17098) (-5564) (-5561) w100 w166 w167
    (by decide +kernel) w100_sound w166_sound w167_sound) (by decide +kernel)
lemma A4_6_6Raw_4_3_1 : (A4_6_6Raw (shape 4 3 1)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 4 3 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 4 3 1)
    (-17098) (0) (-25900) w100 w195 w79
    (by decide +kernel) w100_sound w195_sound w79_sound) (by decide +kernel)
lemma A4_6_6Raw_4_4_0 : (A4_6_6Raw (shape 4 4 0)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 4 4 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 4 4 0)
    (-17098) (-5564) (-56356) w100 w166 w25
    (by decide +kernel) w100_sound w166_sound w25_sound) (by decide +kernel)
lemma A4_6_6Raw_sound (u : Shape) (hu : u ∈ below (shape 4 6 6)) :
    (A4_6_6Raw u).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) u : ℝ) := by
  rw [A4_6_6_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A4_6_6Raw_0_2_6
  · exact A4_6_6Raw_0_3_5
  · exact A4_6_6Raw_0_4_4
  · exact A4_6_6Raw_0_5_3
  · exact A4_6_6Raw_0_6_2
  · exact A4_6_6Raw_1_1_6
  · exact A4_6_6Raw_1_2_5
  · exact A4_6_6Raw_1_3_4
  · exact A4_6_6Raw_1_4_3
  · exact A4_6_6Raw_1_5_2
  · exact A4_6_6Raw_1_6_1
  · exact A4_6_6Raw_2_0_6
  · exact A4_6_6Raw_2_1_5
  · exact A4_6_6Raw_2_2_4
  · exact A4_6_6Raw_2_3_3
  · exact A4_6_6Raw_2_4_2
  · exact A4_6_6Raw_2_5_1
  · exact A4_6_6Raw_2_6_0
  · exact A4_6_6Raw_3_0_5
  · exact A4_6_6Raw_3_1_4
  · exact A4_6_6Raw_3_2_3
  · exact A4_6_6Raw_3_3_2
  · exact A4_6_6Raw_3_4_1
  · exact A4_6_6Raw_3_5_0
  · exact A4_6_6Raw_4_0_4
  · exact A4_6_6Raw_4_1_3
  · exact A4_6_6Raw_4_2_2
  · exact A4_6_6Raw_4_3_1
  · exact A4_6_6Raw_4_4_0
lemma A4_6_6Den_sound : A4_6_6Den.Encloses (((below (shape 4 6 6)).map (splitWeight positiveInitial tableP (shape 4 6 6))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (below (shape 4 6 6)) A4_6_6Raw (splitWeight positiveInitial tableP (shape 4 6 6)) A4_6_6Raw_sound) (by decide +kernel)
lemma A4_6_6Den_positive : 0 < A4_6_6Den.lower := by decide +kernel
lemma A4_6_6Law_check_0_2_6 : contains (.mul (A4_6_6Raw (shape 0 2 6)) (.inv A4_6_6Den)) (A4_6_6Table (shape 0 2 6)) = true := by decide +kernel
lemma A4_6_6Law_check_0_3_5 : contains (.mul (A4_6_6Raw (shape 0 3 5)) (.inv A4_6_6Den)) (A4_6_6Table (shape 0 3 5)) = true := by decide +kernel
lemma A4_6_6Law_check_0_4_4 : contains (.mul (A4_6_6Raw (shape 0 4 4)) (.inv A4_6_6Den)) (A4_6_6Table (shape 0 4 4)) = true := by decide +kernel
lemma A4_6_6Law_check_0_5_3 : contains (.mul (A4_6_6Raw (shape 0 5 3)) (.inv A4_6_6Den)) (A4_6_6Table (shape 0 5 3)) = true := by decide +kernel
lemma A4_6_6Law_check_0_6_2 : contains (.mul (A4_6_6Raw (shape 0 6 2)) (.inv A4_6_6Den)) (A4_6_6Table (shape 0 6 2)) = true := by decide +kernel
lemma A4_6_6Law_check_1_1_6 : contains (.mul (A4_6_6Raw (shape 1 1 6)) (.inv A4_6_6Den)) (A4_6_6Table (shape 1 1 6)) = true := by decide +kernel
lemma A4_6_6Law_check_1_2_5 : contains (.mul (A4_6_6Raw (shape 1 2 5)) (.inv A4_6_6Den)) (A4_6_6Table (shape 1 2 5)) = true := by decide +kernel
lemma A4_6_6Law_check_1_3_4 : contains (.mul (A4_6_6Raw (shape 1 3 4)) (.inv A4_6_6Den)) (A4_6_6Table (shape 1 3 4)) = true := by decide +kernel
lemma A4_6_6Law_check_1_4_3 : contains (.mul (A4_6_6Raw (shape 1 4 3)) (.inv A4_6_6Den)) (A4_6_6Table (shape 1 4 3)) = true := by decide +kernel
lemma A4_6_6Law_check_1_5_2 : contains (.mul (A4_6_6Raw (shape 1 5 2)) (.inv A4_6_6Den)) (A4_6_6Table (shape 1 5 2)) = true := by decide +kernel
lemma A4_6_6Law_check_1_6_1 : contains (.mul (A4_6_6Raw (shape 1 6 1)) (.inv A4_6_6Den)) (A4_6_6Table (shape 1 6 1)) = true := by decide +kernel
lemma A4_6_6Law_check_2_0_6 : contains (.mul (A4_6_6Raw (shape 2 0 6)) (.inv A4_6_6Den)) (A4_6_6Table (shape 2 0 6)) = true := by decide +kernel
lemma A4_6_6Law_check_2_1_5 : contains (.mul (A4_6_6Raw (shape 2 1 5)) (.inv A4_6_6Den)) (A4_6_6Table (shape 2 1 5)) = true := by decide +kernel
lemma A4_6_6Law_check_2_2_4 : contains (.mul (A4_6_6Raw (shape 2 2 4)) (.inv A4_6_6Den)) (A4_6_6Table (shape 2 2 4)) = true := by decide +kernel
lemma A4_6_6Law_check_2_3_3 : contains (.mul (A4_6_6Raw (shape 2 3 3)) (.inv A4_6_6Den)) (A4_6_6Table (shape 2 3 3)) = true := by decide +kernel
lemma A4_6_6Law_check_2_4_2 : contains (.mul (A4_6_6Raw (shape 2 4 2)) (.inv A4_6_6Den)) (A4_6_6Table (shape 2 4 2)) = true := by decide +kernel
lemma A4_6_6Law_check_2_5_1 : contains (.mul (A4_6_6Raw (shape 2 5 1)) (.inv A4_6_6Den)) (A4_6_6Table (shape 2 5 1)) = true := by decide +kernel
lemma A4_6_6Law_check_2_6_0 : contains (.mul (A4_6_6Raw (shape 2 6 0)) (.inv A4_6_6Den)) (A4_6_6Table (shape 2 6 0)) = true := by decide +kernel
lemma A4_6_6Law_check_3_0_5 : contains (.mul (A4_6_6Raw (shape 3 0 5)) (.inv A4_6_6Den)) (A4_6_6Table (shape 3 0 5)) = true := by decide +kernel
lemma A4_6_6Law_check_3_1_4 : contains (.mul (A4_6_6Raw (shape 3 1 4)) (.inv A4_6_6Den)) (A4_6_6Table (shape 3 1 4)) = true := by decide +kernel
lemma A4_6_6Law_check_3_2_3 : contains (.mul (A4_6_6Raw (shape 3 2 3)) (.inv A4_6_6Den)) (A4_6_6Table (shape 3 2 3)) = true := by decide +kernel
lemma A4_6_6Law_check_3_3_2 : contains (.mul (A4_6_6Raw (shape 3 3 2)) (.inv A4_6_6Den)) (A4_6_6Table (shape 3 3 2)) = true := by decide +kernel
lemma A4_6_6Law_check_3_4_1 : contains (.mul (A4_6_6Raw (shape 3 4 1)) (.inv A4_6_6Den)) (A4_6_6Table (shape 3 4 1)) = true := by decide +kernel
lemma A4_6_6Law_check_3_5_0 : contains (.mul (A4_6_6Raw (shape 3 5 0)) (.inv A4_6_6Den)) (A4_6_6Table (shape 3 5 0)) = true := by decide +kernel
lemma A4_6_6Law_check_4_0_4 : contains (.mul (A4_6_6Raw (shape 4 0 4)) (.inv A4_6_6Den)) (A4_6_6Table (shape 4 0 4)) = true := by decide +kernel
lemma A4_6_6Law_check_4_1_3 : contains (.mul (A4_6_6Raw (shape 4 1 3)) (.inv A4_6_6Den)) (A4_6_6Table (shape 4 1 3)) = true := by decide +kernel
lemma A4_6_6Law_check_4_2_2 : contains (.mul (A4_6_6Raw (shape 4 2 2)) (.inv A4_6_6Den)) (A4_6_6Table (shape 4 2 2)) = true := by decide +kernel
lemma A4_6_6Law_check_4_3_1 : contains (.mul (A4_6_6Raw (shape 4 3 1)) (.inv A4_6_6Den)) (A4_6_6Table (shape 4 3 1)) = true := by decide +kernel
lemma A4_6_6Law_check_4_4_0 : contains (.mul (A4_6_6Raw (shape 4 4 0)) (.inv A4_6_6Den)) (A4_6_6Table (shape 4 4 0)) = true := by decide +kernel
lemma A4_6_6Law_check (u : Shape) (hu : u ∈ below (shape 4 6 6)) :
    contains (.mul (A4_6_6Raw u) (.inv A4_6_6Den)) (A4_6_6Table u) = true := by
  rw [A4_6_6_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A4_6_6Law_check_0_2_6
  · exact A4_6_6Law_check_0_3_5
  · exact A4_6_6Law_check_0_4_4
  · exact A4_6_6Law_check_0_5_3
  · exact A4_6_6Law_check_0_6_2
  · exact A4_6_6Law_check_1_1_6
  · exact A4_6_6Law_check_1_2_5
  · exact A4_6_6Law_check_1_3_4
  · exact A4_6_6Law_check_1_4_3
  · exact A4_6_6Law_check_1_5_2
  · exact A4_6_6Law_check_1_6_1
  · exact A4_6_6Law_check_2_0_6
  · exact A4_6_6Law_check_2_1_5
  · exact A4_6_6Law_check_2_2_4
  · exact A4_6_6Law_check_2_3_3
  · exact A4_6_6Law_check_2_4_2
  · exact A4_6_6Law_check_2_5_1
  · exact A4_6_6Law_check_2_6_0
  · exact A4_6_6Law_check_3_0_5
  · exact A4_6_6Law_check_3_1_4
  · exact A4_6_6Law_check_3_2_3
  · exact A4_6_6Law_check_3_3_2
  · exact A4_6_6Law_check_3_4_1
  · exact A4_6_6Law_check_3_5_0
  · exact A4_6_6Law_check_4_0_4
  · exact A4_6_6Law_check_4_1_3
  · exact A4_6_6Law_check_4_2_2
  · exact A4_6_6Law_check_4_3_1
  · exact A4_6_6Law_check_4_4_0
lemma A4_6_6Law_sound_oai (u : Shape) :
    (A4_6_6Law u).Encloses (stageALaw (shape 4 6 6) u : ℝ) := by
  by_cases hu : u ∈ below (shape 4 6 6)
  · have h := contains_sound (Ball.mul_sound (A4_6_6Raw_sound u hu)
      (Ball.inv_sound A4_6_6Den_sound A4_6_6Den_positive)) (A4_6_6Law_check u hu)
    simpa only [A4_6_6Law, hu, ite_true, if_true, stageALaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [A4_6_6Law, hu, ite_false, if_false, stageALaw, splitLaw, Rat.cast_zero]
    simpa only [Rat.cast_zero] using Ball.exact_sound 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A4_6_6Law_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A4_6_6Law_sound_oai
