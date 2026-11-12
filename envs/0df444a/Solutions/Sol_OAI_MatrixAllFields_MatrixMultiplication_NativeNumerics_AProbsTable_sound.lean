-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.AProbsTable_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T06:00:39.101494+00:00
-- url     : https://prove2.me/submissions/229ff4e0-efc2-4c31-80ca-5e464540fd7d

import Mathlib
import Definitions.Def_OAIQ254M003
import Definitions.Def_OAIQ254M005
import Definitions.Def_OAIQ254M006
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_A2_4_10Law_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_A2_6_8Law_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_A2_7_7Law_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_A3_3_10Law_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_A3_5_8Law_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_A3_6_7Law_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_A4_4_8Law_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_A4_5_7Law_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_A4_6_6Law_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_A5_5_6Law_sound

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
lemma w53_sound : w53.Encloses (weight (-34711) : ℝ) := by
  exact weight_enclosed_of_trace (-34711) w53Trace w53S0 w53S1 w53S2 w53S3 w53S4 w53S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w61_sound : w61.Encloses (weight (-32809) : ℝ) := by
  exact weight_enclosed_of_trace (-32809) w61Trace w61S0 w61S1 w61S2 w61S3 w61S4 w61S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w69_sound : w69.Encloses (weight (-28725) : ℝ) := by
  exact weight_enclosed_of_trace (-28725) w69Trace w69S0 w69S1 w69S2 w69S3 w69S4 w69S5
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
lemma w180_sound : w180.Encloses (weight (-3592) : ℝ) := by
  exact weight_enclosed_of_trace (-3592) w180Trace w180S0 w180S1 w180S2 w180S3 w180S4 w180S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w181_sound : w181.Encloses (weight (-3578) : ℝ) := by
  exact weight_enclosed_of_trace (-3578) w181Trace w181S0 w181S1 w181S2 w181S3 w181S4 w181S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w184_sound : w184.Encloses (weight (-3270) : ℝ) := by
  exact weight_enclosed_of_trace (-3270) w184Trace w184S0 w184S1 w184S2 w184S3 w184S4 w184S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w185_sound : w185.Encloses (weight (-3070) : ℝ) := by
  exact weight_enclosed_of_trace (-3070) w185Trace w185S0 w185S1 w185S2 w185S3 w185S4 w185S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w186_sound : w186.Encloses (weight (-2765) : ℝ) := by
  exact weight_enclosed_of_trace (-2765) w186Trace w186S0 w186S1 w186S2 w186S3 w186S4 w186S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w187_sound : w187.Encloses (weight (-2550) : ℝ) := by
  exact weight_enclosed_of_trace (-2550) w187Trace w187S0 w187S1 w187S2 w187S3 w187S4 w187S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w188_sound : w188.Encloses (weight (-2535) : ℝ) := by
  exact weight_enclosed_of_trace (-2535) w188Trace w188S0 w188S1 w188S2 w188S3 w188S4 w188S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w191_sound : w191.Encloses (weight (-1514) : ℝ) := by
  exact weight_enclosed_of_trace (-1514) w191Trace w191S0 w191S1 w191S2 w191S3 w191S4 w191S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w195_sound : w195.Encloses (weight 0 : ℝ) := by
  have he : weight 0 = 1 := by decide +kernel
  rw [he, Rat.cast_one]
  simpa only [w195, Rat.cast_one] using Ball.exact_sound 1

lemma w198_sound : w198.Encloses (weight (295) : ℝ) := by
  exact weight_enclosed_of_trace (295) w198Trace w198S0 w198S1 w198S2 w198S3 w198S4 w198S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

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
lemma w157_sound : w157.Encloses (weight (-6376) : ℝ) := by
  exact weight_enclosed_of_trace (-6376) w157Trace w157S0 w157S1 w157S2 w157S3 w157S4 w157S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w160_sound : w160.Encloses (weight (-5912) : ℝ) := by
  exact weight_enclosed_of_trace (-5912) w160Trace w160S0 w160S1 w160S2 w160S3 w160S4 w160S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w173_sound : w173.Encloses (weight (-4721) : ℝ) := by
  exact weight_enclosed_of_trace (-4721) w173Trace w173S0 w173S1 w173S2 w173S3 w173S4 w173S5
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
lemma w101_sound : w101.Encloses (weight (-16926) : ℝ) := by
  exact weight_enclosed_of_trace (-16926) w101Trace w101S0 w101S1 w101S2 w101S3 w101S4 w101S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w104_sound : w104.Encloses (weight (-16412) : ℝ) := by
  exact weight_enclosed_of_trace (-16412) w104Trace w104S0 w104S1 w104S2 w104S3 w104S4 w104S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w108_sound : w108.Encloses (weight (-16217) : ℝ) := by
  exact weight_enclosed_of_trace (-16217) w108Trace w108S0 w108S1 w108S2 w108S3 w108S4 w108S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w112_sound : w112.Encloses (weight (-15352) : ℝ) := by
  exact weight_enclosed_of_trace (-15352) w112Trace w112S0 w112S1 w112S2 w112S3 w112S4 w112S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w117_sound : w117.Encloses (weight (-14246) : ℝ) := by
  exact weight_enclosed_of_trace (-14246) w117Trace w117S0 w117S1 w117S2 w117S3 w117S4 w117S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w120_sound : w120.Encloses (weight (-13519) : ℝ) := by
  exact weight_enclosed_of_trace (-13519) w120Trace w120S0 w120S1 w120S2 w120S3 w120S4 w120S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

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
lemma positiveInitial_list : positiveInitial = [
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

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitA1_1_14
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
lemma A1_1_14_below : below (shape 1 1 14) = [
  (shape 0 0 8),
  (shape 0 1 7),
  (shape 1 0 7),
  (shape 1 1 6)] := by decide +kernel
lemma A1_1_14Raw_0_0_8 : (A1_1_14Raw (shape 0 0 8)).Encloses (splitWeight positiveInitial tableP (shape 1 1 14) (shape 0 0 8) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 1 14) (shape 0 0 8)
    (0) (0) (-3070) w195 w195 w185
    (by decide +kernel) w195_sound w195_sound w185_sound) (by decide +kernel)
lemma A1_1_14Raw_0_1_7 : (A1_1_14Raw (shape 0 1 7)).Encloses (splitWeight positiveInitial tableP (shape 1 1 14) (shape 0 1 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 1 14) (shape 0 1 7)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A1_1_14Raw_1_0_7 : (A1_1_14Raw (shape 1 0 7)).Encloses (splitWeight positiveInitial tableP (shape 1 1 14) (shape 1 0 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 1 14) (shape 1 0 7)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A1_1_14Raw_1_1_6 : (A1_1_14Raw (shape 1 1 6)).Encloses (splitWeight positiveInitial tableP (shape 1 1 14) (shape 1 1 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 1 14) (shape 1 1 6)
    (0) (0) (-3070) w195 w195 w185
    (by decide +kernel) w195_sound w195_sound w185_sound) (by decide +kernel)
lemma A1_1_14Raw_sound (u : Shape) (hu : u ∈ below (shape 1 1 14)) :
    (A1_1_14Raw u).Encloses (splitWeight positiveInitial tableP (shape 1 1 14) u : ℝ) := by
  rw [A1_1_14_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl
  · exact A1_1_14Raw_0_0_8
  · exact A1_1_14Raw_0_1_7
  · exact A1_1_14Raw_1_0_7
  · exact A1_1_14Raw_1_1_6
lemma A1_1_14Den_sound : A1_1_14Den.Encloses (((below (shape 1 1 14)).map (splitWeight positiveInitial tableP (shape 1 1 14))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (below (shape 1 1 14)) A1_1_14Raw (splitWeight positiveInitial tableP (shape 1 1 14)) A1_1_14Raw_sound) (by decide +kernel)
lemma A1_1_14Den_positive : 0 < A1_1_14Den.lower := by decide +kernel
lemma A1_1_14Law_check_0_0_8 : contains (.mul (A1_1_14Raw (shape 0 0 8)) (.inv A1_1_14Den)) (A1_1_14Table (shape 0 0 8)) = true := by decide +kernel
lemma A1_1_14Law_check_0_1_7 : contains (.mul (A1_1_14Raw (shape 0 1 7)) (.inv A1_1_14Den)) (A1_1_14Table (shape 0 1 7)) = true := by decide +kernel
lemma A1_1_14Law_check_1_0_7 : contains (.mul (A1_1_14Raw (shape 1 0 7)) (.inv A1_1_14Den)) (A1_1_14Table (shape 1 0 7)) = true := by decide +kernel
lemma A1_1_14Law_check_1_1_6 : contains (.mul (A1_1_14Raw (shape 1 1 6)) (.inv A1_1_14Den)) (A1_1_14Table (shape 1 1 6)) = true := by decide +kernel
lemma A1_1_14Law_check (u : Shape) (hu : u ∈ below (shape 1 1 14)) :
    contains (.mul (A1_1_14Raw u) (.inv A1_1_14Den)) (A1_1_14Table u) = true := by
  rw [A1_1_14_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl
  · exact A1_1_14Law_check_0_0_8
  · exact A1_1_14Law_check_0_1_7
  · exact A1_1_14Law_check_1_0_7
  · exact A1_1_14Law_check_1_1_6
lemma A1_1_14Law_sound (u : Shape) :
    (A1_1_14Law u).Encloses (stageALaw (shape 1 1 14) u : ℝ) := by
  by_cases hu : u ∈ below (shape 1 1 14)
  · have h := contains_sound (Ball.mul_sound (A1_1_14Raw_sound u hu)
      (Ball.inv_sound A1_1_14Den_sound A1_1_14Den_positive)) (A1_1_14Law_check u hu)
    simpa only [A1_1_14Law, hu, ite_true, if_true, stageALaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [A1_1_14Law, hu, ite_false, if_false, stageALaw, splitLaw, Rat.cast_zero]
    simpa only [Rat.cast_zero] using Ball.exact_sound 0

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
lemma w28_sound : w28.Encloses (weight (-55230) : ℝ) := by
  exact weight_enclosed_of_trace (-55230) w28Trace w28S0 w28S1 w28S2 w28S3 w28S4 w28S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w33_sound : w33.Encloses (weight (-53221) : ℝ) := by
  exact weight_enclosed_of_trace (-53221) w33Trace w33S0 w33S1 w33S2 w33S3 w33S4 w33S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w36_sound : w36.Encloses (weight (-49297) : ℝ) := by
  exact weight_enclosed_of_trace (-49297) w36Trace w36S0 w36S1 w36S2 w36S3 w36S4 w36S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w37_sound : w37.Encloses (weight (-47439) : ℝ) := by
  exact weight_enclosed_of_trace (-47439) w37Trace w37S0 w37S1 w37S2 w37S3 w37S4 w37S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w38_sound : w38.Encloses (weight (-46871) : ℝ) := by
  exact weight_enclosed_of_trace (-46871) w38Trace w38S0 w38S1 w38S2 w38S3 w38S4 w38S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w39_sound : w39.Encloses (weight (-46655) : ℝ) := by
  exact weight_enclosed_of_trace (-46655) w39Trace w39S0 w39S1 w39S2 w39S3 w39S4 w39S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w47_sound : w47.Encloses (weight (-38211) : ℝ) := by
  exact weight_enclosed_of_trace (-38211) w47Trace w47S0 w47S1 w47S2 w47S3 w47S4 w47S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

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
lemma w134_sound : w134.Encloses (weight (-9654) : ℝ) := by
  exact weight_enclosed_of_trace (-9654) w134Trace w134S0 w134S1 w134S2 w134S3 w134S4 w134S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w135_sound : w135.Encloses (weight (-9643) : ℝ) := by
  exact weight_enclosed_of_trace (-9643) w135Trace w135S0 w135S1 w135S2 w135S3 w135S4 w135S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w137_sound : w137.Encloses (weight (-8700) : ℝ) := by
  exact weight_enclosed_of_trace (-8700) w137Trace w137S0 w137S1 w137S2 w137S3 w137S4 w137S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w138_sound : w138.Encloses (weight (-8576) : ℝ) := by
  exact weight_enclosed_of_trace (-8576) w138Trace w138S0 w138S1 w138S2 w138S3 w138S4 w138S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w142_sound : w142.Encloses (weight (-7530) : ℝ) := by
  exact weight_enclosed_of_trace (-7530) w142Trace w142S0 w142S1 w142S2 w142S3 w142S4 w142S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w144_sound : w144.Encloses (weight (-7447) : ℝ) := by
  exact weight_enclosed_of_trace (-7447) w144Trace w144S0 w144S1 w144S2 w144S3 w144S4 w144S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w147_sound : w147.Encloses (weight (-7207) : ℝ) := by
  exact weight_enclosed_of_trace (-7207) w147Trace w147S0 w147S1 w147S2 w147S3 w147S4 w147S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w149_sound : w149.Encloses (weight (-7009) : ℝ) := by
  exact weight_enclosed_of_trace (-7009) w149Trace w149S0 w149S1 w149S2 w149S3 w149S4 w149S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
lemma A1_3_12_below : below (shape 1 3 12) = [
  (shape 0 0 8),
  (shape 0 1 7),
  (shape 0 2 6),
  (shape 0 3 5),
  (shape 1 0 7),
  (shape 1 1 6),
  (shape 1 2 5),
  (shape 1 3 4)] := by decide +kernel
lemma A1_3_12Raw_0_0_8 : (A1_3_12Raw (shape 0 0 8)).Encloses (splitWeight positiveInitial tableP (shape 1 3 12) (shape 0 0 8) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 3 12) (shape 0 0 8)
    (0) (-1514) (-38211) w195 w191 w47
    (by decide +kernel) w195_sound w191_sound w47_sound) (by decide +kernel)
lemma A1_3_12Raw_0_1_7 : (A1_3_12Raw (shape 0 1 7)).Encloses (splitWeight positiveInitial tableP (shape 1 3 12) (shape 0 1 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 3 12) (shape 0 1 7)
    (0) (0) (-9654) w195 w195 w134
    (by decide +kernel) w195_sound w195_sound w134_sound) (by decide +kernel)
lemma A1_3_12Raw_0_2_6 : (A1_3_12Raw (shape 0 2 6)).Encloses (splitWeight positiveInitial tableP (shape 1 3 12) (shape 0 2 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 3 12) (shape 0 2 6)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A1_3_12Raw_0_3_5 : (A1_3_12Raw (shape 0 3 5)).Encloses (splitWeight positiveInitial tableP (shape 1 3 12) (shape 0 3 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 3 12) (shape 0 3 5)
    (0) (-1514) (-9654) w195 w191 w134
    (by decide +kernel) w195_sound w191_sound w134_sound) (by decide +kernel)
lemma A1_3_12Raw_1_0_7 : (A1_3_12Raw (shape 1 0 7)).Encloses (splitWeight positiveInitial tableP (shape 1 3 12) (shape 1 0 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 3 12) (shape 1 0 7)
    (0) (-1514) (-9654) w195 w191 w134
    (by decide +kernel) w195_sound w191_sound w134_sound) (by decide +kernel)
lemma A1_3_12Raw_1_1_6 : (A1_3_12Raw (shape 1 1 6)).Encloses (splitWeight positiveInitial tableP (shape 1 3 12) (shape 1 1 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 3 12) (shape 1 1 6)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A1_3_12Raw_1_2_5 : (A1_3_12Raw (shape 1 2 5)).Encloses (splitWeight positiveInitial tableP (shape 1 3 12) (shape 1 2 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 3 12) (shape 1 2 5)
    (0) (0) (-9654) w195 w195 w134
    (by decide +kernel) w195_sound w195_sound w134_sound) (by decide +kernel)
lemma A1_3_12Raw_1_3_4 : (A1_3_12Raw (shape 1 3 4)).Encloses (splitWeight positiveInitial tableP (shape 1 3 12) (shape 1 3 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 3 12) (shape 1 3 4)
    (0) (-1514) (-38211) w195 w191 w47
    (by decide +kernel) w195_sound w191_sound w47_sound) (by decide +kernel)
lemma A1_3_12Raw_sound (u : Shape) (hu : u ∈ below (shape 1 3 12)) :
    (A1_3_12Raw u).Encloses (splitWeight positiveInitial tableP (shape 1 3 12) u : ℝ) := by
  rw [A1_3_12_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A1_3_12Raw_0_0_8
  · exact A1_3_12Raw_0_1_7
  · exact A1_3_12Raw_0_2_6
  · exact A1_3_12Raw_0_3_5
  · exact A1_3_12Raw_1_0_7
  · exact A1_3_12Raw_1_1_6
  · exact A1_3_12Raw_1_2_5
  · exact A1_3_12Raw_1_3_4
lemma A1_3_12Den_sound : A1_3_12Den.Encloses (((below (shape 1 3 12)).map (splitWeight positiveInitial tableP (shape 1 3 12))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (below (shape 1 3 12)) A1_3_12Raw (splitWeight positiveInitial tableP (shape 1 3 12)) A1_3_12Raw_sound) (by decide +kernel)
lemma A1_3_12Den_positive : 0 < A1_3_12Den.lower := by decide +kernel
lemma A1_3_12Law_check_0_0_8 : contains (.mul (A1_3_12Raw (shape 0 0 8)) (.inv A1_3_12Den)) (A1_3_12Table (shape 0 0 8)) = true := by decide +kernel
lemma A1_3_12Law_check_0_1_7 : contains (.mul (A1_3_12Raw (shape 0 1 7)) (.inv A1_3_12Den)) (A1_3_12Table (shape 0 1 7)) = true := by decide +kernel
lemma A1_3_12Law_check_0_2_6 : contains (.mul (A1_3_12Raw (shape 0 2 6)) (.inv A1_3_12Den)) (A1_3_12Table (shape 0 2 6)) = true := by decide +kernel
lemma A1_3_12Law_check_0_3_5 : contains (.mul (A1_3_12Raw (shape 0 3 5)) (.inv A1_3_12Den)) (A1_3_12Table (shape 0 3 5)) = true := by decide +kernel
lemma A1_3_12Law_check_1_0_7 : contains (.mul (A1_3_12Raw (shape 1 0 7)) (.inv A1_3_12Den)) (A1_3_12Table (shape 1 0 7)) = true := by decide +kernel
lemma A1_3_12Law_check_1_1_6 : contains (.mul (A1_3_12Raw (shape 1 1 6)) (.inv A1_3_12Den)) (A1_3_12Table (shape 1 1 6)) = true := by decide +kernel
lemma A1_3_12Law_check_1_2_5 : contains (.mul (A1_3_12Raw (shape 1 2 5)) (.inv A1_3_12Den)) (A1_3_12Table (shape 1 2 5)) = true := by decide +kernel
lemma A1_3_12Law_check_1_3_4 : contains (.mul (A1_3_12Raw (shape 1 3 4)) (.inv A1_3_12Den)) (A1_3_12Table (shape 1 3 4)) = true := by decide +kernel
lemma A1_3_12Law_check (u : Shape) (hu : u ∈ below (shape 1 3 12)) :
    contains (.mul (A1_3_12Raw u) (.inv A1_3_12Den)) (A1_3_12Table u) = true := by
  rw [A1_3_12_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A1_3_12Law_check_0_0_8
  · exact A1_3_12Law_check_0_1_7
  · exact A1_3_12Law_check_0_2_6
  · exact A1_3_12Law_check_0_3_5
  · exact A1_3_12Law_check_1_0_7
  · exact A1_3_12Law_check_1_1_6
  · exact A1_3_12Law_check_1_2_5
  · exact A1_3_12Law_check_1_3_4
lemma A1_3_12Law_sound (u : Shape) :
    (A1_3_12Law u).Encloses (stageALaw (shape 1 3 12) u : ℝ) := by
  by_cases hu : u ∈ below (shape 1 3 12)
  · have h := contains_sound (Ball.mul_sound (A1_3_12Raw_sound u hu)
      (Ball.inv_sound A1_3_12Den_sound A1_3_12Den_positive)) (A1_3_12Law_check u hu)
    simpa only [A1_3_12Law, hu, ite_true, if_true, stageALaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [A1_3_12Law, hu, ite_false, if_false, stageALaw, splitLaw, Rat.cast_zero]
    simpa only [Rat.cast_zero] using Ball.exact_sound 0

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitA1_4_11
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
lemma A1_4_11_below : below (shape 1 4 11) = [
  (shape 0 0 8),
  (shape 0 1 7),
  (shape 0 2 6),
  (shape 0 3 5),
  (shape 0 4 4),
  (shape 1 0 7),
  (shape 1 1 6),
  (shape 1 2 5),
  (shape 1 3 4),
  (shape 1 4 3)] := by decide +kernel
lemma A1_4_11Raw_0_0_8 : (A1_4_11Raw (shape 0 0 8)).Encloses (splitWeight positiveInitial tableP (shape 1 4 11) (shape 0 0 8) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 4 11) (shape 0 0 8)
    (0) (-7530) (-55230) w195 w142 w28
    (by decide +kernel) w195_sound w142_sound w28_sound) (by decide +kernel)
lemma A1_4_11Raw_0_1_7 : (A1_4_11Raw (shape 0 1 7)).Encloses (splitWeight positiveInitial tableP (shape 1 4 11) (shape 0 1 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 4 11) (shape 0 1 7)
    (0) (-2765) (-16412) w195 w186 w104
    (by decide +kernel) w195_sound w186_sound w104_sound) (by decide +kernel)
lemma A1_4_11Raw_0_2_6 : (A1_4_11Raw (shape 0 2 6)).Encloses (splitWeight positiveInitial tableP (shape 1 4 11) (shape 0 2 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 4 11) (shape 0 2 6)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A1_4_11Raw_0_3_5 : (A1_4_11Raw (shape 0 3 5)).Encloses (splitWeight positiveInitial tableP (shape 1 4 11) (shape 0 3 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 4 11) (shape 0 3 5)
    (0) (-2765) (0) w195 w186 w195
    (by decide +kernel) w195_sound w186_sound w195_sound) (by decide +kernel)
lemma A1_4_11Raw_0_4_4 : (A1_4_11Raw (shape 0 4 4)).Encloses (splitWeight positiveInitial tableP (shape 1 4 11) (shape 0 4 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 4 11) (shape 0 4 4)
    (0) (-7530) (-16412) w195 w142 w104
    (by decide +kernel) w195_sound w142_sound w104_sound) (by decide +kernel)
lemma A1_4_11Raw_1_0_7 : (A1_4_11Raw (shape 1 0 7)).Encloses (splitWeight positiveInitial tableP (shape 1 4 11) (shape 1 0 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 4 11) (shape 1 0 7)
    (0) (-7530) (-16412) w195 w142 w104
    (by decide +kernel) w195_sound w142_sound w104_sound) (by decide +kernel)
lemma A1_4_11Raw_1_1_6 : (A1_4_11Raw (shape 1 1 6)).Encloses (splitWeight positiveInitial tableP (shape 1 4 11) (shape 1 1 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 4 11) (shape 1 1 6)
    (0) (-2765) (0) w195 w186 w195
    (by decide +kernel) w195_sound w186_sound w195_sound) (by decide +kernel)
lemma A1_4_11Raw_1_2_5 : (A1_4_11Raw (shape 1 2 5)).Encloses (splitWeight positiveInitial tableP (shape 1 4 11) (shape 1 2 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 4 11) (shape 1 2 5)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A1_4_11Raw_1_3_4 : (A1_4_11Raw (shape 1 3 4)).Encloses (splitWeight positiveInitial tableP (shape 1 4 11) (shape 1 3 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 4 11) (shape 1 3 4)
    (0) (-2765) (-16412) w195 w186 w104
    (by decide +kernel) w195_sound w186_sound w104_sound) (by decide +kernel)
lemma A1_4_11Raw_1_4_3 : (A1_4_11Raw (shape 1 4 3)).Encloses (splitWeight positiveInitial tableP (shape 1 4 11) (shape 1 4 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 4 11) (shape 1 4 3)
    (0) (-7530) (-55230) w195 w142 w28
    (by decide +kernel) w195_sound w142_sound w28_sound) (by decide +kernel)
lemma A1_4_11Raw_sound (u : Shape) (hu : u ∈ below (shape 1 4 11)) :
    (A1_4_11Raw u).Encloses (splitWeight positiveInitial tableP (shape 1 4 11) u : ℝ) := by
  rw [A1_4_11_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A1_4_11Raw_0_0_8
  · exact A1_4_11Raw_0_1_7
  · exact A1_4_11Raw_0_2_6
  · exact A1_4_11Raw_0_3_5
  · exact A1_4_11Raw_0_4_4
  · exact A1_4_11Raw_1_0_7
  · exact A1_4_11Raw_1_1_6
  · exact A1_4_11Raw_1_2_5
  · exact A1_4_11Raw_1_3_4
  · exact A1_4_11Raw_1_4_3
lemma A1_4_11Den_sound : A1_4_11Den.Encloses (((below (shape 1 4 11)).map (splitWeight positiveInitial tableP (shape 1 4 11))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (below (shape 1 4 11)) A1_4_11Raw (splitWeight positiveInitial tableP (shape 1 4 11)) A1_4_11Raw_sound) (by decide +kernel)
lemma A1_4_11Den_positive : 0 < A1_4_11Den.lower := by decide +kernel
lemma A1_4_11Law_check_0_0_8 : contains (.mul (A1_4_11Raw (shape 0 0 8)) (.inv A1_4_11Den)) (A1_4_11Table (shape 0 0 8)) = true := by decide +kernel
lemma A1_4_11Law_check_0_1_7 : contains (.mul (A1_4_11Raw (shape 0 1 7)) (.inv A1_4_11Den)) (A1_4_11Table (shape 0 1 7)) = true := by decide +kernel
lemma A1_4_11Law_check_0_2_6 : contains (.mul (A1_4_11Raw (shape 0 2 6)) (.inv A1_4_11Den)) (A1_4_11Table (shape 0 2 6)) = true := by decide +kernel
lemma A1_4_11Law_check_0_3_5 : contains (.mul (A1_4_11Raw (shape 0 3 5)) (.inv A1_4_11Den)) (A1_4_11Table (shape 0 3 5)) = true := by decide +kernel
lemma A1_4_11Law_check_0_4_4 : contains (.mul (A1_4_11Raw (shape 0 4 4)) (.inv A1_4_11Den)) (A1_4_11Table (shape 0 4 4)) = true := by decide +kernel
lemma A1_4_11Law_check_1_0_7 : contains (.mul (A1_4_11Raw (shape 1 0 7)) (.inv A1_4_11Den)) (A1_4_11Table (shape 1 0 7)) = true := by decide +kernel
lemma A1_4_11Law_check_1_1_6 : contains (.mul (A1_4_11Raw (shape 1 1 6)) (.inv A1_4_11Den)) (A1_4_11Table (shape 1 1 6)) = true := by decide +kernel
lemma A1_4_11Law_check_1_2_5 : contains (.mul (A1_4_11Raw (shape 1 2 5)) (.inv A1_4_11Den)) (A1_4_11Table (shape 1 2 5)) = true := by decide +kernel
lemma A1_4_11Law_check_1_3_4 : contains (.mul (A1_4_11Raw (shape 1 3 4)) (.inv A1_4_11Den)) (A1_4_11Table (shape 1 3 4)) = true := by decide +kernel
lemma A1_4_11Law_check_1_4_3 : contains (.mul (A1_4_11Raw (shape 1 4 3)) (.inv A1_4_11Den)) (A1_4_11Table (shape 1 4 3)) = true := by decide +kernel
lemma A1_4_11Law_check (u : Shape) (hu : u ∈ below (shape 1 4 11)) :
    contains (.mul (A1_4_11Raw u) (.inv A1_4_11Den)) (A1_4_11Table u) = true := by
  rw [A1_4_11_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A1_4_11Law_check_0_0_8
  · exact A1_4_11Law_check_0_1_7
  · exact A1_4_11Law_check_0_2_6
  · exact A1_4_11Law_check_0_3_5
  · exact A1_4_11Law_check_0_4_4
  · exact A1_4_11Law_check_1_0_7
  · exact A1_4_11Law_check_1_1_6
  · exact A1_4_11Law_check_1_2_5
  · exact A1_4_11Law_check_1_3_4
  · exact A1_4_11Law_check_1_4_3
lemma A1_4_11Law_sound (u : Shape) :
    (A1_4_11Law u).Encloses (stageALaw (shape 1 4 11) u : ℝ) := by
  by_cases hu : u ∈ below (shape 1 4 11)
  · have h := contains_sound (Ball.mul_sound (A1_4_11Raw_sound u hu)
      (Ball.inv_sound A1_4_11Den_sound A1_4_11Den_positive)) (A1_4_11Law_check u hu)
    simpa only [A1_4_11Law, hu, ite_true, if_true, stageALaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [A1_4_11Law, hu, ite_false, if_false, stageALaw, splitLaw, Rat.cast_zero]
    simpa only [Rat.cast_zero] using Ball.exact_sound 0

end MatrixMultiplication.NativeNumerics

end
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
lemma w76_sound : w76.Encloses (weight (-26324) : ℝ) := by
  exact weight_enclosed_of_trace (-26324) w76Trace w76S0 w76S1 w76S2 w76S3 w76S4 w76S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w80_sound : w80.Encloses (weight (-25058) : ℝ) := by
  exact weight_enclosed_of_trace (-25058) w80Trace w80S0 w80S1 w80S2 w80S3 w80S4 w80S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w82_sound : w82.Encloses (weight (-24599) : ℝ) := by
  exact weight_enclosed_of_trace (-24599) w82Trace w82S0 w82S1 w82S2 w82S3 w82S4 w82S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w84_sound : w84.Encloses (weight (-20546) : ℝ) := by
  exact weight_enclosed_of_trace (-20546) w84Trace w84S0 w84S1 w84S2 w84S3 w84S4 w84S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w95_sound : w95.Encloses (weight (-17874) : ℝ) := by
  exact weight_enclosed_of_trace (-17874) w95Trace w95S0 w95S1 w95S2 w95S3 w95S4 w95S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w97_sound : w97.Encloses (weight (-17336) : ℝ) := by
  exact weight_enclosed_of_trace (-17336) w97Trace w97S0 w97S1 w97S2 w97S3 w97S4 w97S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma A1_2_13_below : below (shape 1 2 13) = [
  (shape 0 0 8),
  (shape 0 1 7),
  (shape 0 2 6),
  (shape 1 0 7),
  (shape 1 1 6),
  (shape 1 2 5)] := by decide +kernel
lemma A1_2_13Raw_0_0_8 : (A1_2_13Raw (shape 0 0 8)).Encloses (splitWeight positiveInitial tableP (shape 1 2 13) (shape 0 0 8) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 2 13) (shape 0 0 8)
    (0) (295) (-20546) w195 w198 w84
    (by decide +kernel) w195_sound w198_sound w84_sound) (by decide +kernel)
lemma A1_2_13Raw_0_1_7 : (A1_2_13Raw (shape 0 1 7)).Encloses (splitWeight positiveInitial tableP (shape 1 2 13) (shape 0 1 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 2 13) (shape 0 1 7)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A1_2_13Raw_0_2_6 : (A1_2_13Raw (shape 0 2 6)).Encloses (splitWeight positiveInitial tableP (shape 1 2 13) (shape 0 2 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 2 13) (shape 0 2 6)
    (0) (295) (0) w195 w198 w195
    (by decide +kernel) w195_sound w198_sound w195_sound) (by decide +kernel)
lemma A1_2_13Raw_1_0_7 : (A1_2_13Raw (shape 1 0 7)).Encloses (splitWeight positiveInitial tableP (shape 1 2 13) (shape 1 0 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 2 13) (shape 1 0 7)
    (0) (295) (0) w195 w198 w195
    (by decide +kernel) w195_sound w198_sound w195_sound) (by decide +kernel)
lemma A1_2_13Raw_1_1_6 : (A1_2_13Raw (shape 1 1 6)).Encloses (splitWeight positiveInitial tableP (shape 1 2 13) (shape 1 1 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 2 13) (shape 1 1 6)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A1_2_13Raw_1_2_5 : (A1_2_13Raw (shape 1 2 5)).Encloses (splitWeight positiveInitial tableP (shape 1 2 13) (shape 1 2 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 2 13) (shape 1 2 5)
    (0) (295) (-20546) w195 w198 w84
    (by decide +kernel) w195_sound w198_sound w84_sound) (by decide +kernel)
lemma A1_2_13Raw_sound (u : Shape) (hu : u ∈ below (shape 1 2 13)) :
    (A1_2_13Raw u).Encloses (splitWeight positiveInitial tableP (shape 1 2 13) u : ℝ) := by
  rw [A1_2_13_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · exact A1_2_13Raw_0_0_8
  · exact A1_2_13Raw_0_1_7
  · exact A1_2_13Raw_0_2_6
  · exact A1_2_13Raw_1_0_7
  · exact A1_2_13Raw_1_1_6
  · exact A1_2_13Raw_1_2_5
lemma A1_2_13Den_sound : A1_2_13Den.Encloses (((below (shape 1 2 13)).map (splitWeight positiveInitial tableP (shape 1 2 13))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (below (shape 1 2 13)) A1_2_13Raw (splitWeight positiveInitial tableP (shape 1 2 13)) A1_2_13Raw_sound) (by decide +kernel)
lemma A1_2_13Den_positive : 0 < A1_2_13Den.lower := by decide +kernel
lemma A1_2_13Law_check_0_0_8 : contains (.mul (A1_2_13Raw (shape 0 0 8)) (.inv A1_2_13Den)) (A1_2_13Table (shape 0 0 8)) = true := by decide +kernel
lemma A1_2_13Law_check_0_1_7 : contains (.mul (A1_2_13Raw (shape 0 1 7)) (.inv A1_2_13Den)) (A1_2_13Table (shape 0 1 7)) = true := by decide +kernel
lemma A1_2_13Law_check_0_2_6 : contains (.mul (A1_2_13Raw (shape 0 2 6)) (.inv A1_2_13Den)) (A1_2_13Table (shape 0 2 6)) = true := by decide +kernel
lemma A1_2_13Law_check_1_0_7 : contains (.mul (A1_2_13Raw (shape 1 0 7)) (.inv A1_2_13Den)) (A1_2_13Table (shape 1 0 7)) = true := by decide +kernel
lemma A1_2_13Law_check_1_1_6 : contains (.mul (A1_2_13Raw (shape 1 1 6)) (.inv A1_2_13Den)) (A1_2_13Table (shape 1 1 6)) = true := by decide +kernel
lemma A1_2_13Law_check_1_2_5 : contains (.mul (A1_2_13Raw (shape 1 2 5)) (.inv A1_2_13Den)) (A1_2_13Table (shape 1 2 5)) = true := by decide +kernel
lemma A1_2_13Law_check (u : Shape) (hu : u ∈ below (shape 1 2 13)) :
    contains (.mul (A1_2_13Raw u) (.inv A1_2_13Den)) (A1_2_13Table u) = true := by
  rw [A1_2_13_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · exact A1_2_13Law_check_0_0_8
  · exact A1_2_13Law_check_0_1_7
  · exact A1_2_13Law_check_0_2_6
  · exact A1_2_13Law_check_1_0_7
  · exact A1_2_13Law_check_1_1_6
  · exact A1_2_13Law_check_1_2_5
lemma A1_2_13Law_sound (u : Shape) :
    (A1_2_13Law u).Encloses (stageALaw (shape 1 2 13) u : ℝ) := by
  by_cases hu : u ∈ below (shape 1 2 13)
  · have h := contains_sound (Ball.mul_sound (A1_2_13Raw_sound u hu)
      (Ball.inv_sound A1_2_13Den_sound A1_2_13Den_positive)) (A1_2_13Law_check u hu)
    simpa only [A1_2_13Law, hu, ite_true, if_true, stageALaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [A1_2_13Law, hu, ite_false, if_false, stageALaw, splitLaw, Rat.cast_zero]
    simpa only [Rat.cast_zero] using Ball.exact_sound 0

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
lemma w3_sound : w3.Encloses (weight (-96770) : ℝ) := by
  exact weight_enclosed_of_trace (-96770) w3Trace w3S0 w3S1 w3S2 w3S3 w3S4 w3S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w4_sound : w4.Encloses (weight (-96458) : ℝ) := by
  exact weight_enclosed_of_trace (-96458) w4Trace w4S0 w4S1 w4S2 w4S3 w4S4 w4S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w5_sound : w5.Encloses (weight (-95643) : ℝ) := by
  exact weight_enclosed_of_trace (-95643) w5Trace w5S0 w5S1 w5S2 w5S3 w5S4 w5S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w6_sound : w6.Encloses (weight (-92989) : ℝ) := by
  exact weight_enclosed_of_trace (-92989) w6Trace w6S0 w6S1 w6S2 w6S3 w6S4 w6S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w8_sound : w8.Encloses (weight (-78106) : ℝ) := by
  exact weight_enclosed_of_trace (-78106) w8Trace w8S0 w8S1 w8S2 w8S3 w8S4 w8S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w19_sound : w19.Encloses (weight (-62269) : ℝ) := by
  exact weight_enclosed_of_trace (-62269) w19Trace w19S0 w19S1 w19S2 w19S3 w19S4 w19S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma A1_5_10_below : below (shape 1 5 10) = [
  (shape 0 0 8),
  (shape 0 1 7),
  (shape 0 2 6),
  (shape 0 3 5),
  (shape 0 4 4),
  (shape 0 5 3),
  (shape 1 0 7),
  (shape 1 1 6),
  (shape 1 2 5),
  (shape 1 3 4),
  (shape 1 4 3),
  (shape 1 5 2)] := by decide +kernel
lemma A1_5_10Raw_0_0_8 : (A1_5_10Raw (shape 0 0 8)).Encloses (splitWeight positiveInitial tableP (shape 1 5 10) (shape 0 0 8) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 5 10) (shape 0 0 8)
    (0) (-14246) (-78106) w195 w117 w8
    (by decide +kernel) w195_sound w117_sound w8_sound) (by decide +kernel)
lemma A1_5_10Raw_0_1_7 : (A1_5_10Raw (shape 0 1 7)).Encloses (splitWeight positiveInitial tableP (shape 1 5 10) (shape 0 1 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 5 10) (shape 0 1 7)
    (0) (-5912) (-32809) w195 w160 w61
    (by decide +kernel) w195_sound w160_sound w61_sound) (by decide +kernel)
lemma A1_5_10Raw_0_2_6 : (A1_5_10Raw (shape 0 2 6)).Encloses (splitWeight positiveInitial tableP (shape 1 5 10) (shape 0 2 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 5 10) (shape 0 2 6)
    (0) (0) (-7009) w195 w195 w149
    (by decide +kernel) w195_sound w195_sound w149_sound) (by decide +kernel)
lemma A1_5_10Raw_0_3_5 : (A1_5_10Raw (shape 0 3 5)).Encloses (splitWeight positiveInitial tableP (shape 1 5 10) (shape 0 3 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 5 10) (shape 0 3 5)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A1_5_10Raw_0_4_4 : (A1_5_10Raw (shape 0 4 4)).Encloses (splitWeight positiveInitial tableP (shape 1 5 10) (shape 0 4 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 5 10) (shape 0 4 4)
    (0) (-5912) (-7009) w195 w160 w149
    (by decide +kernel) w195_sound w160_sound w149_sound) (by decide +kernel)
lemma A1_5_10Raw_0_5_3 : (A1_5_10Raw (shape 0 5 3)).Encloses (splitWeight positiveInitial tableP (shape 1 5 10) (shape 0 5 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 5 10) (shape 0 5 3)
    (0) (-14246) (-32809) w195 w117 w61
    (by decide +kernel) w195_sound w117_sound w61_sound) (by decide +kernel)
lemma A1_5_10Raw_1_0_7 : (A1_5_10Raw (shape 1 0 7)).Encloses (splitWeight positiveInitial tableP (shape 1 5 10) (shape 1 0 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 5 10) (shape 1 0 7)
    (0) (-14246) (-32809) w195 w117 w61
    (by decide +kernel) w195_sound w117_sound w61_sound) (by decide +kernel)
lemma A1_5_10Raw_1_1_6 : (A1_5_10Raw (shape 1 1 6)).Encloses (splitWeight positiveInitial tableP (shape 1 5 10) (shape 1 1 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 5 10) (shape 1 1 6)
    (0) (-5912) (-7009) w195 w160 w149
    (by decide +kernel) w195_sound w160_sound w149_sound) (by decide +kernel)
lemma A1_5_10Raw_1_2_5 : (A1_5_10Raw (shape 1 2 5)).Encloses (splitWeight positiveInitial tableP (shape 1 5 10) (shape 1 2 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 5 10) (shape 1 2 5)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A1_5_10Raw_1_3_4 : (A1_5_10Raw (shape 1 3 4)).Encloses (splitWeight positiveInitial tableP (shape 1 5 10) (shape 1 3 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 5 10) (shape 1 3 4)
    (0) (0) (-7009) w195 w195 w149
    (by decide +kernel) w195_sound w195_sound w149_sound) (by decide +kernel)
lemma A1_5_10Raw_1_4_3 : (A1_5_10Raw (shape 1 4 3)).Encloses (splitWeight positiveInitial tableP (shape 1 5 10) (shape 1 4 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 5 10) (shape 1 4 3)
    (0) (-5912) (-32809) w195 w160 w61
    (by decide +kernel) w195_sound w160_sound w61_sound) (by decide +kernel)
lemma A1_5_10Raw_1_5_2 : (A1_5_10Raw (shape 1 5 2)).Encloses (splitWeight positiveInitial tableP (shape 1 5 10) (shape 1 5 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 5 10) (shape 1 5 2)
    (0) (-14246) (-78106) w195 w117 w8
    (by decide +kernel) w195_sound w117_sound w8_sound) (by decide +kernel)
lemma A1_5_10Raw_sound (u : Shape) (hu : u ∈ below (shape 1 5 10)) :
    (A1_5_10Raw u).Encloses (splitWeight positiveInitial tableP (shape 1 5 10) u : ℝ) := by
  rw [A1_5_10_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A1_5_10Raw_0_0_8
  · exact A1_5_10Raw_0_1_7
  · exact A1_5_10Raw_0_2_6
  · exact A1_5_10Raw_0_3_5
  · exact A1_5_10Raw_0_4_4
  · exact A1_5_10Raw_0_5_3
  · exact A1_5_10Raw_1_0_7
  · exact A1_5_10Raw_1_1_6
  · exact A1_5_10Raw_1_2_5
  · exact A1_5_10Raw_1_3_4
  · exact A1_5_10Raw_1_4_3
  · exact A1_5_10Raw_1_5_2
lemma A1_5_10Den_sound : A1_5_10Den.Encloses (((below (shape 1 5 10)).map (splitWeight positiveInitial tableP (shape 1 5 10))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (below (shape 1 5 10)) A1_5_10Raw (splitWeight positiveInitial tableP (shape 1 5 10)) A1_5_10Raw_sound) (by decide +kernel)
lemma A1_5_10Den_positive : 0 < A1_5_10Den.lower := by decide +kernel
lemma A1_5_10Law_check_0_0_8 : contains (.mul (A1_5_10Raw (shape 0 0 8)) (.inv A1_5_10Den)) (A1_5_10Table (shape 0 0 8)) = true := by decide +kernel
lemma A1_5_10Law_check_0_1_7 : contains (.mul (A1_5_10Raw (shape 0 1 7)) (.inv A1_5_10Den)) (A1_5_10Table (shape 0 1 7)) = true := by decide +kernel
lemma A1_5_10Law_check_0_2_6 : contains (.mul (A1_5_10Raw (shape 0 2 6)) (.inv A1_5_10Den)) (A1_5_10Table (shape 0 2 6)) = true := by decide +kernel
lemma A1_5_10Law_check_0_3_5 : contains (.mul (A1_5_10Raw (shape 0 3 5)) (.inv A1_5_10Den)) (A1_5_10Table (shape 0 3 5)) = true := by decide +kernel
lemma A1_5_10Law_check_0_4_4 : contains (.mul (A1_5_10Raw (shape 0 4 4)) (.inv A1_5_10Den)) (A1_5_10Table (shape 0 4 4)) = true := by decide +kernel
lemma A1_5_10Law_check_0_5_3 : contains (.mul (A1_5_10Raw (shape 0 5 3)) (.inv A1_5_10Den)) (A1_5_10Table (shape 0 5 3)) = true := by decide +kernel
lemma A1_5_10Law_check_1_0_7 : contains (.mul (A1_5_10Raw (shape 1 0 7)) (.inv A1_5_10Den)) (A1_5_10Table (shape 1 0 7)) = true := by decide +kernel
lemma A1_5_10Law_check_1_1_6 : contains (.mul (A1_5_10Raw (shape 1 1 6)) (.inv A1_5_10Den)) (A1_5_10Table (shape 1 1 6)) = true := by decide +kernel
lemma A1_5_10Law_check_1_2_5 : contains (.mul (A1_5_10Raw (shape 1 2 5)) (.inv A1_5_10Den)) (A1_5_10Table (shape 1 2 5)) = true := by decide +kernel
lemma A1_5_10Law_check_1_3_4 : contains (.mul (A1_5_10Raw (shape 1 3 4)) (.inv A1_5_10Den)) (A1_5_10Table (shape 1 3 4)) = true := by decide +kernel
lemma A1_5_10Law_check_1_4_3 : contains (.mul (A1_5_10Raw (shape 1 4 3)) (.inv A1_5_10Den)) (A1_5_10Table (shape 1 4 3)) = true := by decide +kernel
lemma A1_5_10Law_check_1_5_2 : contains (.mul (A1_5_10Raw (shape 1 5 2)) (.inv A1_5_10Den)) (A1_5_10Table (shape 1 5 2)) = true := by decide +kernel
lemma A1_5_10Law_check (u : Shape) (hu : u ∈ below (shape 1 5 10)) :
    contains (.mul (A1_5_10Raw u) (.inv A1_5_10Den)) (A1_5_10Table u) = true := by
  rw [A1_5_10_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A1_5_10Law_check_0_0_8
  · exact A1_5_10Law_check_0_1_7
  · exact A1_5_10Law_check_0_2_6
  · exact A1_5_10Law_check_0_3_5
  · exact A1_5_10Law_check_0_4_4
  · exact A1_5_10Law_check_0_5_3
  · exact A1_5_10Law_check_1_0_7
  · exact A1_5_10Law_check_1_1_6
  · exact A1_5_10Law_check_1_2_5
  · exact A1_5_10Law_check_1_3_4
  · exact A1_5_10Law_check_1_4_3
  · exact A1_5_10Law_check_1_5_2
lemma A1_5_10Law_sound (u : Shape) :
    (A1_5_10Law u).Encloses (stageALaw (shape 1 5 10) u : ℝ) := by
  by_cases hu : u ∈ below (shape 1 5 10)
  · have h := contains_sound (Ball.mul_sound (A1_5_10Raw_sound u hu)
      (Ball.inv_sound A1_5_10Den_sound A1_5_10Den_positive)) (A1_5_10Law_check u hu)
    simpa only [A1_5_10Law, hu, ite_true, if_true, stageALaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [A1_5_10Law, hu, ite_false, if_false, stageALaw, splitLaw, Rat.cast_zero]
    simpa only [Rat.cast_zero] using Ball.exact_sound 0

lemma A1_6_9_below : below (shape 1 6 9) = [
  (shape 0 0 8),
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
  (shape 1 6 1)] := by decide +kernel
lemma A1_6_9Raw_0_0_8 : (A1_6_9Raw (shape 0 0 8)).Encloses (splitWeight positiveInitial tableP (shape 1 6 9) (shape 0 0 8) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 6 9) (shape 0 0 8)
    (0) (-26324) (-96458) w195 w76 w4
    (by decide +kernel) w195_sound w76_sound w4_sound) (by decide +kernel)
lemma A1_6_9Raw_0_1_7 : (A1_6_9Raw (shape 0 1 7)).Encloses (splitWeight positiveInitial tableP (shape 1 6 9) (shape 0 1 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 6 9) (shape 0 1 7)
    (0) (-13519) (-47439) w195 w120 w37
    (by decide +kernel) w195_sound w120_sound w37_sound) (by decide +kernel)
lemma A1_6_9Raw_0_2_6 : (A1_6_9Raw (shape 0 2 6)).Encloses (splitWeight positiveInitial tableP (shape 1 6 9) (shape 0 2 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 6 9) (shape 0 2 6)
    (0) (-3592) (-16217) w195 w180 w108
    (by decide +kernel) w195_sound w180_sound w108_sound) (by decide +kernel)
lemma A1_6_9Raw_0_3_5 : (A1_6_9Raw (shape 0 3 5)).Encloses (splitWeight positiveInitial tableP (shape 1 6 9) (shape 0 3 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 6 9) (shape 0 3 5)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A1_6_9Raw_0_4_4 : (A1_6_9Raw (shape 0 4 4)).Encloses (splitWeight positiveInitial tableP (shape 1 6 9) (shape 0 4 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 6 9) (shape 0 4 4)
    (0) (-3592) (0) w195 w180 w195
    (by decide +kernel) w195_sound w180_sound w195_sound) (by decide +kernel)
lemma A1_6_9Raw_0_5_3 : (A1_6_9Raw (shape 0 5 3)).Encloses (splitWeight positiveInitial tableP (shape 1 6 9) (shape 0 5 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 6 9) (shape 0 5 3)
    (0) (-13519) (-16217) w195 w120 w108
    (by decide +kernel) w195_sound w120_sound w108_sound) (by decide +kernel)
lemma A1_6_9Raw_0_6_2 : (A1_6_9Raw (shape 0 6 2)).Encloses (splitWeight positiveInitial tableP (shape 1 6 9) (shape 0 6 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 6 9) (shape 0 6 2)
    (0) (-26324) (-47439) w195 w76 w37
    (by decide +kernel) w195_sound w76_sound w37_sound) (by decide +kernel)
lemma A1_6_9Raw_1_0_7 : (A1_6_9Raw (shape 1 0 7)).Encloses (splitWeight positiveInitial tableP (shape 1 6 9) (shape 1 0 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 6 9) (shape 1 0 7)
    (0) (-26324) (-47439) w195 w76 w37
    (by decide +kernel) w195_sound w76_sound w37_sound) (by decide +kernel)
lemma A1_6_9Raw_1_1_6 : (A1_6_9Raw (shape 1 1 6)).Encloses (splitWeight positiveInitial tableP (shape 1 6 9) (shape 1 1 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 6 9) (shape 1 1 6)
    (0) (-13519) (-16217) w195 w120 w108
    (by decide +kernel) w195_sound w120_sound w108_sound) (by decide +kernel)
lemma A1_6_9Raw_1_2_5 : (A1_6_9Raw (shape 1 2 5)).Encloses (splitWeight positiveInitial tableP (shape 1 6 9) (shape 1 2 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 6 9) (shape 1 2 5)
    (0) (-3592) (0) w195 w180 w195
    (by decide +kernel) w195_sound w180_sound w195_sound) (by decide +kernel)
lemma A1_6_9Raw_1_3_4 : (A1_6_9Raw (shape 1 3 4)).Encloses (splitWeight positiveInitial tableP (shape 1 6 9) (shape 1 3 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 6 9) (shape 1 3 4)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A1_6_9Raw_1_4_3 : (A1_6_9Raw (shape 1 4 3)).Encloses (splitWeight positiveInitial tableP (shape 1 6 9) (shape 1 4 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 6 9) (shape 1 4 3)
    (0) (-3592) (-16217) w195 w180 w108
    (by decide +kernel) w195_sound w180_sound w108_sound) (by decide +kernel)
lemma A1_6_9Raw_1_5_2 : (A1_6_9Raw (shape 1 5 2)).Encloses (splitWeight positiveInitial tableP (shape 1 6 9) (shape 1 5 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 6 9) (shape 1 5 2)
    (0) (-13519) (-47439) w195 w120 w37
    (by decide +kernel) w195_sound w120_sound w37_sound) (by decide +kernel)
lemma A1_6_9Raw_1_6_1 : (A1_6_9Raw (shape 1 6 1)).Encloses (splitWeight positiveInitial tableP (shape 1 6 9) (shape 1 6 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 6 9) (shape 1 6 1)
    (0) (-26324) (-96458) w195 w76 w4
    (by decide +kernel) w195_sound w76_sound w4_sound) (by decide +kernel)
lemma A1_6_9Raw_sound (u : Shape) (hu : u ∈ below (shape 1 6 9)) :
    (A1_6_9Raw u).Encloses (splitWeight positiveInitial tableP (shape 1 6 9) u : ℝ) := by
  rw [A1_6_9_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A1_6_9Raw_0_0_8
  · exact A1_6_9Raw_0_1_7
  · exact A1_6_9Raw_0_2_6
  · exact A1_6_9Raw_0_3_5
  · exact A1_6_9Raw_0_4_4
  · exact A1_6_9Raw_0_5_3
  · exact A1_6_9Raw_0_6_2
  · exact A1_6_9Raw_1_0_7
  · exact A1_6_9Raw_1_1_6
  · exact A1_6_9Raw_1_2_5
  · exact A1_6_9Raw_1_3_4
  · exact A1_6_9Raw_1_4_3
  · exact A1_6_9Raw_1_5_2
  · exact A1_6_9Raw_1_6_1
lemma A1_6_9Den_sound : A1_6_9Den.Encloses (((below (shape 1 6 9)).map (splitWeight positiveInitial tableP (shape 1 6 9))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (below (shape 1 6 9)) A1_6_9Raw (splitWeight positiveInitial tableP (shape 1 6 9)) A1_6_9Raw_sound) (by decide +kernel)
lemma A1_6_9Den_positive : 0 < A1_6_9Den.lower := by decide +kernel
lemma A1_6_9Law_check_0_0_8 : contains (.mul (A1_6_9Raw (shape 0 0 8)) (.inv A1_6_9Den)) (A1_6_9Table (shape 0 0 8)) = true := by decide +kernel
lemma A1_6_9Law_check_0_1_7 : contains (.mul (A1_6_9Raw (shape 0 1 7)) (.inv A1_6_9Den)) (A1_6_9Table (shape 0 1 7)) = true := by decide +kernel
lemma A1_6_9Law_check_0_2_6 : contains (.mul (A1_6_9Raw (shape 0 2 6)) (.inv A1_6_9Den)) (A1_6_9Table (shape 0 2 6)) = true := by decide +kernel
lemma A1_6_9Law_check_0_3_5 : contains (.mul (A1_6_9Raw (shape 0 3 5)) (.inv A1_6_9Den)) (A1_6_9Table (shape 0 3 5)) = true := by decide +kernel
lemma A1_6_9Law_check_0_4_4 : contains (.mul (A1_6_9Raw (shape 0 4 4)) (.inv A1_6_9Den)) (A1_6_9Table (shape 0 4 4)) = true := by decide +kernel
lemma A1_6_9Law_check_0_5_3 : contains (.mul (A1_6_9Raw (shape 0 5 3)) (.inv A1_6_9Den)) (A1_6_9Table (shape 0 5 3)) = true := by decide +kernel
lemma A1_6_9Law_check_0_6_2 : contains (.mul (A1_6_9Raw (shape 0 6 2)) (.inv A1_6_9Den)) (A1_6_9Table (shape 0 6 2)) = true := by decide +kernel
lemma A1_6_9Law_check_1_0_7 : contains (.mul (A1_6_9Raw (shape 1 0 7)) (.inv A1_6_9Den)) (A1_6_9Table (shape 1 0 7)) = true := by decide +kernel
lemma A1_6_9Law_check_1_1_6 : contains (.mul (A1_6_9Raw (shape 1 1 6)) (.inv A1_6_9Den)) (A1_6_9Table (shape 1 1 6)) = true := by decide +kernel
lemma A1_6_9Law_check_1_2_5 : contains (.mul (A1_6_9Raw (shape 1 2 5)) (.inv A1_6_9Den)) (A1_6_9Table (shape 1 2 5)) = true := by decide +kernel
lemma A1_6_9Law_check_1_3_4 : contains (.mul (A1_6_9Raw (shape 1 3 4)) (.inv A1_6_9Den)) (A1_6_9Table (shape 1 3 4)) = true := by decide +kernel
lemma A1_6_9Law_check_1_4_3 : contains (.mul (A1_6_9Raw (shape 1 4 3)) (.inv A1_6_9Den)) (A1_6_9Table (shape 1 4 3)) = true := by decide +kernel
lemma A1_6_9Law_check_1_5_2 : contains (.mul (A1_6_9Raw (shape 1 5 2)) (.inv A1_6_9Den)) (A1_6_9Table (shape 1 5 2)) = true := by decide +kernel
lemma A1_6_9Law_check_1_6_1 : contains (.mul (A1_6_9Raw (shape 1 6 1)) (.inv A1_6_9Den)) (A1_6_9Table (shape 1 6 1)) = true := by decide +kernel
lemma A1_6_9Law_check (u : Shape) (hu : u ∈ below (shape 1 6 9)) :
    contains (.mul (A1_6_9Raw u) (.inv A1_6_9Den)) (A1_6_9Table u) = true := by
  rw [A1_6_9_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A1_6_9Law_check_0_0_8
  · exact A1_6_9Law_check_0_1_7
  · exact A1_6_9Law_check_0_2_6
  · exact A1_6_9Law_check_0_3_5
  · exact A1_6_9Law_check_0_4_4
  · exact A1_6_9Law_check_0_5_3
  · exact A1_6_9Law_check_0_6_2
  · exact A1_6_9Law_check_1_0_7
  · exact A1_6_9Law_check_1_1_6
  · exact A1_6_9Law_check_1_2_5
  · exact A1_6_9Law_check_1_3_4
  · exact A1_6_9Law_check_1_4_3
  · exact A1_6_9Law_check_1_5_2
  · exact A1_6_9Law_check_1_6_1
lemma A1_6_9Law_sound (u : Shape) :
    (A1_6_9Law u).Encloses (stageALaw (shape 1 6 9) u : ℝ) := by
  by_cases hu : u ∈ below (shape 1 6 9)
  · have h := contains_sound (Ball.mul_sound (A1_6_9Raw_sound u hu)
      (Ball.inv_sound A1_6_9Den_sound A1_6_9Den_positive)) (A1_6_9Law_check u hu)
    simpa only [A1_6_9Law, hu, ite_true, if_true, stageALaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [A1_6_9Law, hu, ite_false, if_false, stageALaw, splitLaw, Rat.cast_zero]
    simpa only [Rat.cast_zero] using Ball.exact_sound 0

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitA1_7_8
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
lemma A1_7_8_below : below (shape 1 7 8) = [
  (shape 0 0 8),
  (shape 0 1 7),
  (shape 0 2 6),
  (shape 0 3 5),
  (shape 0 4 4),
  (shape 0 5 3),
  (shape 0 6 2),
  (shape 0 7 1),
  (shape 1 0 7),
  (shape 1 1 6),
  (shape 1 2 5),
  (shape 1 3 4),
  (shape 1 4 3),
  (shape 1 5 2),
  (shape 1 6 1),
  (shape 1 7 0)] := by decide +kernel
lemma A1_7_8Raw_0_0_8 : (A1_7_8Raw (shape 0 0 8)).Encloses (splitWeight positiveInitial tableP (shape 1 7 8) (shape 0 0 8) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 7 8) (shape 0 0 8)
    (0) (-46871) (-95643) w195 w38 w5
    (by decide +kernel) w195_sound w38_sound w5_sound) (by decide +kernel)
lemma A1_7_8Raw_0_1_7 : (A1_7_8Raw (shape 0 1 7)).Encloses (splitWeight positiveInitial tableP (shape 1 7 8) (shape 0 1 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 7 8) (shape 0 1 7)
    (0) (-25058) (-62269) w195 w80 w19
    (by decide +kernel) w195_sound w80_sound w19_sound) (by decide +kernel)
lemma A1_7_8Raw_0_2_6 : (A1_7_8Raw (shape 0 2 6)).Encloses (splitWeight positiveInitial tableP (shape 1 7 8) (shape 0 2 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 7 8) (shape 0 2 6)
    (0) (-9643) (-28725) w195 w135 w69
    (by decide +kernel) w195_sound w135_sound w69_sound) (by decide +kernel)
lemma A1_7_8Raw_0_3_5 : (A1_7_8Raw (shape 0 3 5)).Encloses (splitWeight positiveInitial tableP (shape 1 7 8) (shape 0 3 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 7 8) (shape 0 3 5)
    (0) (0) (-8576) w195 w195 w138
    (by decide +kernel) w195_sound w195_sound w138_sound) (by decide +kernel)
lemma A1_7_8Raw_0_4_4 : (A1_7_8Raw (shape 0 4 4)).Encloses (splitWeight positiveInitial tableP (shape 1 7 8) (shape 0 4 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 7 8) (shape 0 4 4)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A1_7_8Raw_0_5_3 : (A1_7_8Raw (shape 0 5 3)).Encloses (splitWeight positiveInitial tableP (shape 1 7 8) (shape 0 5 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 7 8) (shape 0 5 3)
    (0) (-9643) (-8576) w195 w135 w138
    (by decide +kernel) w195_sound w135_sound w138_sound) (by decide +kernel)
lemma A1_7_8Raw_0_6_2 : (A1_7_8Raw (shape 0 6 2)).Encloses (splitWeight positiveInitial tableP (shape 1 7 8) (shape 0 6 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 7 8) (shape 0 6 2)
    (0) (-25058) (-28725) w195 w80 w69
    (by decide +kernel) w195_sound w80_sound w69_sound) (by decide +kernel)
lemma A1_7_8Raw_0_7_1 : (A1_7_8Raw (shape 0 7 1)).Encloses (splitWeight positiveInitial tableP (shape 1 7 8) (shape 0 7 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 7 8) (shape 0 7 1)
    (0) (-46871) (-62269) w195 w38 w19
    (by decide +kernel) w195_sound w38_sound w19_sound) (by decide +kernel)
lemma A1_7_8Raw_1_0_7 : (A1_7_8Raw (shape 1 0 7)).Encloses (splitWeight positiveInitial tableP (shape 1 7 8) (shape 1 0 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 7 8) (shape 1 0 7)
    (0) (-46871) (-62269) w195 w38 w19
    (by decide +kernel) w195_sound w38_sound w19_sound) (by decide +kernel)
lemma A1_7_8Raw_1_1_6 : (A1_7_8Raw (shape 1 1 6)).Encloses (splitWeight positiveInitial tableP (shape 1 7 8) (shape 1 1 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 7 8) (shape 1 1 6)
    (0) (-25058) (-28725) w195 w80 w69
    (by decide +kernel) w195_sound w80_sound w69_sound) (by decide +kernel)
lemma A1_7_8Raw_1_2_5 : (A1_7_8Raw (shape 1 2 5)).Encloses (splitWeight positiveInitial tableP (shape 1 7 8) (shape 1 2 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 7 8) (shape 1 2 5)
    (0) (-9643) (-8576) w195 w135 w138
    (by decide +kernel) w195_sound w135_sound w138_sound) (by decide +kernel)
lemma A1_7_8Raw_1_3_4 : (A1_7_8Raw (shape 1 3 4)).Encloses (splitWeight positiveInitial tableP (shape 1 7 8) (shape 1 3 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 7 8) (shape 1 3 4)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A1_7_8Raw_1_4_3 : (A1_7_8Raw (shape 1 4 3)).Encloses (splitWeight positiveInitial tableP (shape 1 7 8) (shape 1 4 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 7 8) (shape 1 4 3)
    (0) (0) (-8576) w195 w195 w138
    (by decide +kernel) w195_sound w195_sound w138_sound) (by decide +kernel)
lemma A1_7_8Raw_1_5_2 : (A1_7_8Raw (shape 1 5 2)).Encloses (splitWeight positiveInitial tableP (shape 1 7 8) (shape 1 5 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 7 8) (shape 1 5 2)
    (0) (-9643) (-28725) w195 w135 w69
    (by decide +kernel) w195_sound w135_sound w69_sound) (by decide +kernel)
lemma A1_7_8Raw_1_6_1 : (A1_7_8Raw (shape 1 6 1)).Encloses (splitWeight positiveInitial tableP (shape 1 7 8) (shape 1 6 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 7 8) (shape 1 6 1)
    (0) (-25058) (-62269) w195 w80 w19
    (by decide +kernel) w195_sound w80_sound w19_sound) (by decide +kernel)
lemma A1_7_8Raw_1_7_0 : (A1_7_8Raw (shape 1 7 0)).Encloses (splitWeight positiveInitial tableP (shape 1 7 8) (shape 1 7 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 7 8) (shape 1 7 0)
    (0) (-46871) (-95643) w195 w38 w5
    (by decide +kernel) w195_sound w38_sound w5_sound) (by decide +kernel)
lemma A1_7_8Raw_sound (u : Shape) (hu : u ∈ below (shape 1 7 8)) :
    (A1_7_8Raw u).Encloses (splitWeight positiveInitial tableP (shape 1 7 8) u : ℝ) := by
  rw [A1_7_8_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A1_7_8Raw_0_0_8
  · exact A1_7_8Raw_0_1_7
  · exact A1_7_8Raw_0_2_6
  · exact A1_7_8Raw_0_3_5
  · exact A1_7_8Raw_0_4_4
  · exact A1_7_8Raw_0_5_3
  · exact A1_7_8Raw_0_6_2
  · exact A1_7_8Raw_0_7_1
  · exact A1_7_8Raw_1_0_7
  · exact A1_7_8Raw_1_1_6
  · exact A1_7_8Raw_1_2_5
  · exact A1_7_8Raw_1_3_4
  · exact A1_7_8Raw_1_4_3
  · exact A1_7_8Raw_1_5_2
  · exact A1_7_8Raw_1_6_1
  · exact A1_7_8Raw_1_7_0
lemma A1_7_8Den_sound : A1_7_8Den.Encloses (((below (shape 1 7 8)).map (splitWeight positiveInitial tableP (shape 1 7 8))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (below (shape 1 7 8)) A1_7_8Raw (splitWeight positiveInitial tableP (shape 1 7 8)) A1_7_8Raw_sound) (by decide +kernel)
lemma A1_7_8Den_positive : 0 < A1_7_8Den.lower := by decide +kernel
lemma A1_7_8Law_check_0_0_8 : contains (.mul (A1_7_8Raw (shape 0 0 8)) (.inv A1_7_8Den)) (A1_7_8Table (shape 0 0 8)) = true := by decide +kernel
lemma A1_7_8Law_check_0_1_7 : contains (.mul (A1_7_8Raw (shape 0 1 7)) (.inv A1_7_8Den)) (A1_7_8Table (shape 0 1 7)) = true := by decide +kernel
lemma A1_7_8Law_check_0_2_6 : contains (.mul (A1_7_8Raw (shape 0 2 6)) (.inv A1_7_8Den)) (A1_7_8Table (shape 0 2 6)) = true := by decide +kernel
lemma A1_7_8Law_check_0_3_5 : contains (.mul (A1_7_8Raw (shape 0 3 5)) (.inv A1_7_8Den)) (A1_7_8Table (shape 0 3 5)) = true := by decide +kernel
lemma A1_7_8Law_check_0_4_4 : contains (.mul (A1_7_8Raw (shape 0 4 4)) (.inv A1_7_8Den)) (A1_7_8Table (shape 0 4 4)) = true := by decide +kernel
lemma A1_7_8Law_check_0_5_3 : contains (.mul (A1_7_8Raw (shape 0 5 3)) (.inv A1_7_8Den)) (A1_7_8Table (shape 0 5 3)) = true := by decide +kernel
lemma A1_7_8Law_check_0_6_2 : contains (.mul (A1_7_8Raw (shape 0 6 2)) (.inv A1_7_8Den)) (A1_7_8Table (shape 0 6 2)) = true := by decide +kernel
lemma A1_7_8Law_check_0_7_1 : contains (.mul (A1_7_8Raw (shape 0 7 1)) (.inv A1_7_8Den)) (A1_7_8Table (shape 0 7 1)) = true := by decide +kernel
lemma A1_7_8Law_check_1_0_7 : contains (.mul (A1_7_8Raw (shape 1 0 7)) (.inv A1_7_8Den)) (A1_7_8Table (shape 1 0 7)) = true := by decide +kernel
lemma A1_7_8Law_check_1_1_6 : contains (.mul (A1_7_8Raw (shape 1 1 6)) (.inv A1_7_8Den)) (A1_7_8Table (shape 1 1 6)) = true := by decide +kernel
lemma A1_7_8Law_check_1_2_5 : contains (.mul (A1_7_8Raw (shape 1 2 5)) (.inv A1_7_8Den)) (A1_7_8Table (shape 1 2 5)) = true := by decide +kernel
lemma A1_7_8Law_check_1_3_4 : contains (.mul (A1_7_8Raw (shape 1 3 4)) (.inv A1_7_8Den)) (A1_7_8Table (shape 1 3 4)) = true := by decide +kernel
lemma A1_7_8Law_check_1_4_3 : contains (.mul (A1_7_8Raw (shape 1 4 3)) (.inv A1_7_8Den)) (A1_7_8Table (shape 1 4 3)) = true := by decide +kernel
lemma A1_7_8Law_check_1_5_2 : contains (.mul (A1_7_8Raw (shape 1 5 2)) (.inv A1_7_8Den)) (A1_7_8Table (shape 1 5 2)) = true := by decide +kernel
lemma A1_7_8Law_check_1_6_1 : contains (.mul (A1_7_8Raw (shape 1 6 1)) (.inv A1_7_8Den)) (A1_7_8Table (shape 1 6 1)) = true := by decide +kernel
lemma A1_7_8Law_check_1_7_0 : contains (.mul (A1_7_8Raw (shape 1 7 0)) (.inv A1_7_8Den)) (A1_7_8Table (shape 1 7 0)) = true := by decide +kernel
lemma A1_7_8Law_check (u : Shape) (hu : u ∈ below (shape 1 7 8)) :
    contains (.mul (A1_7_8Raw u) (.inv A1_7_8Den)) (A1_7_8Table u) = true := by
  rw [A1_7_8_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A1_7_8Law_check_0_0_8
  · exact A1_7_8Law_check_0_1_7
  · exact A1_7_8Law_check_0_2_6
  · exact A1_7_8Law_check_0_3_5
  · exact A1_7_8Law_check_0_4_4
  · exact A1_7_8Law_check_0_5_3
  · exact A1_7_8Law_check_0_6_2
  · exact A1_7_8Law_check_0_7_1
  · exact A1_7_8Law_check_1_0_7
  · exact A1_7_8Law_check_1_1_6
  · exact A1_7_8Law_check_1_2_5
  · exact A1_7_8Law_check_1_3_4
  · exact A1_7_8Law_check_1_4_3
  · exact A1_7_8Law_check_1_5_2
  · exact A1_7_8Law_check_1_6_1
  · exact A1_7_8Law_check_1_7_0
lemma A1_7_8Law_sound (u : Shape) :
    (A1_7_8Law u).Encloses (stageALaw (shape 1 7 8) u : ℝ) := by
  by_cases hu : u ∈ below (shape 1 7 8)
  · have h := contains_sound (Ball.mul_sound (A1_7_8Raw_sound u hu)
      (Ball.inv_sound A1_7_8Den_sound A1_7_8Den_positive)) (A1_7_8Law_check u hu)
    simpa only [A1_7_8Law, hu, ite_true, if_true, stageALaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [A1_7_8Law, hu, ite_false, if_false, stageALaw, splitLaw, Rat.cast_zero]
    simpa only [Rat.cast_zero] using Ball.exact_sound 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitA2_2_12
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
lemma A2_2_12_below : below (shape 2 2 12) = [
  (shape 0 0 8),
  (shape 0 1 7),
  (shape 0 2 6),
  (shape 1 0 7),
  (shape 1 1 6),
  (shape 1 2 5),
  (shape 2 0 6),
  (shape 2 1 5),
  (shape 2 2 4)] := by decide +kernel
lemma A2_2_12Raw_0_0_8 : (A2_2_12Raw (shape 0 0 8)).Encloses (splitWeight positiveInitial tableP (shape 2 2 12) (shape 0 0 8) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 2 12) (shape 0 0 8)
    (-2535) (-2550) (-34711) w188 w187 w53
    (by decide +kernel) w188_sound w187_sound w53_sound) (by decide +kernel)
lemma A2_2_12Raw_0_1_7 : (A2_2_12Raw (shape 0 1 7)).Encloses (splitWeight positiveInitial tableP (shape 2 2 12) (shape 0 1 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 2 12) (shape 0 1 7)
    (-2535) (0) (-7207) w188 w195 w147
    (by decide +kernel) w188_sound w195_sound w147_sound) (by decide +kernel)
lemma A2_2_12Raw_0_2_6 : (A2_2_12Raw (shape 0 2 6)).Encloses (splitWeight positiveInitial tableP (shape 2 2 12) (shape 0 2 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 2 12) (shape 0 2 6)
    (-2535) (-2550) (0) w188 w187 w195
    (by decide +kernel) w188_sound w187_sound w195_sound) (by decide +kernel)
lemma A2_2_12Raw_1_0_7 : (A2_2_12Raw (shape 1 0 7)).Encloses (splitWeight positiveInitial tableP (shape 2 2 12) (shape 1 0 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 2 12) (shape 1 0 7)
    (0) (-2550) (-7207) w195 w187 w147
    (by decide +kernel) w195_sound w187_sound w147_sound) (by decide +kernel)
lemma A2_2_12Raw_1_1_6 : (A2_2_12Raw (shape 1 1 6)).Encloses (splitWeight positiveInitial tableP (shape 2 2 12) (shape 1 1 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 2 12) (shape 1 1 6)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A2_2_12Raw_1_2_5 : (A2_2_12Raw (shape 1 2 5)).Encloses (splitWeight positiveInitial tableP (shape 2 2 12) (shape 1 2 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 2 12) (shape 1 2 5)
    (0) (-2550) (-7207) w195 w187 w147
    (by decide +kernel) w195_sound w187_sound w147_sound) (by decide +kernel)
lemma A2_2_12Raw_2_0_6 : (A2_2_12Raw (shape 2 0 6)).Encloses (splitWeight positiveInitial tableP (shape 2 2 12) (shape 2 0 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 2 12) (shape 2 0 6)
    (-2535) (-2550) (0) w188 w187 w195
    (by decide +kernel) w188_sound w187_sound w195_sound) (by decide +kernel)
lemma A2_2_12Raw_2_1_5 : (A2_2_12Raw (shape 2 1 5)).Encloses (splitWeight positiveInitial tableP (shape 2 2 12) (shape 2 1 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 2 12) (shape 2 1 5)
    (-2535) (0) (-7207) w188 w195 w147
    (by decide +kernel) w188_sound w195_sound w147_sound) (by decide +kernel)
lemma A2_2_12Raw_2_2_4 : (A2_2_12Raw (shape 2 2 4)).Encloses (splitWeight positiveInitial tableP (shape 2 2 12) (shape 2 2 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 2 12) (shape 2 2 4)
    (-2535) (-2550) (-34711) w188 w187 w53
    (by decide +kernel) w188_sound w187_sound w53_sound) (by decide +kernel)
lemma A2_2_12Raw_sound (u : Shape) (hu : u ∈ below (shape 2 2 12)) :
    (A2_2_12Raw u).Encloses (splitWeight positiveInitial tableP (shape 2 2 12) u : ℝ) := by
  rw [A2_2_12_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A2_2_12Raw_0_0_8
  · exact A2_2_12Raw_0_1_7
  · exact A2_2_12Raw_0_2_6
  · exact A2_2_12Raw_1_0_7
  · exact A2_2_12Raw_1_1_6
  · exact A2_2_12Raw_1_2_5
  · exact A2_2_12Raw_2_0_6
  · exact A2_2_12Raw_2_1_5
  · exact A2_2_12Raw_2_2_4
lemma A2_2_12Den_sound : A2_2_12Den.Encloses (((below (shape 2 2 12)).map (splitWeight positiveInitial tableP (shape 2 2 12))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (below (shape 2 2 12)) A2_2_12Raw (splitWeight positiveInitial tableP (shape 2 2 12)) A2_2_12Raw_sound) (by decide +kernel)
lemma A2_2_12Den_positive : 0 < A2_2_12Den.lower := by decide +kernel
lemma A2_2_12Law_check_0_0_8 : contains (.mul (A2_2_12Raw (shape 0 0 8)) (.inv A2_2_12Den)) (A2_2_12Table (shape 0 0 8)) = true := by decide +kernel
lemma A2_2_12Law_check_0_1_7 : contains (.mul (A2_2_12Raw (shape 0 1 7)) (.inv A2_2_12Den)) (A2_2_12Table (shape 0 1 7)) = true := by decide +kernel
lemma A2_2_12Law_check_0_2_6 : contains (.mul (A2_2_12Raw (shape 0 2 6)) (.inv A2_2_12Den)) (A2_2_12Table (shape 0 2 6)) = true := by decide +kernel
lemma A2_2_12Law_check_1_0_7 : contains (.mul (A2_2_12Raw (shape 1 0 7)) (.inv A2_2_12Den)) (A2_2_12Table (shape 1 0 7)) = true := by decide +kernel
lemma A2_2_12Law_check_1_1_6 : contains (.mul (A2_2_12Raw (shape 1 1 6)) (.inv A2_2_12Den)) (A2_2_12Table (shape 1 1 6)) = true := by decide +kernel
lemma A2_2_12Law_check_1_2_5 : contains (.mul (A2_2_12Raw (shape 1 2 5)) (.inv A2_2_12Den)) (A2_2_12Table (shape 1 2 5)) = true := by decide +kernel
lemma A2_2_12Law_check_2_0_6 : contains (.mul (A2_2_12Raw (shape 2 0 6)) (.inv A2_2_12Den)) (A2_2_12Table (shape 2 0 6)) = true := by decide +kernel
lemma A2_2_12Law_check_2_1_5 : contains (.mul (A2_2_12Raw (shape 2 1 5)) (.inv A2_2_12Den)) (A2_2_12Table (shape 2 1 5)) = true := by decide +kernel
lemma A2_2_12Law_check_2_2_4 : contains (.mul (A2_2_12Raw (shape 2 2 4)) (.inv A2_2_12Den)) (A2_2_12Table (shape 2 2 4)) = true := by decide +kernel
lemma A2_2_12Law_check (u : Shape) (hu : u ∈ below (shape 2 2 12)) :
    contains (.mul (A2_2_12Raw u) (.inv A2_2_12Den)) (A2_2_12Table u) = true := by
  rw [A2_2_12_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A2_2_12Law_check_0_0_8
  · exact A2_2_12Law_check_0_1_7
  · exact A2_2_12Law_check_0_2_6
  · exact A2_2_12Law_check_1_0_7
  · exact A2_2_12Law_check_1_1_6
  · exact A2_2_12Law_check_1_2_5
  · exact A2_2_12Law_check_2_0_6
  · exact A2_2_12Law_check_2_1_5
  · exact A2_2_12Law_check_2_2_4
lemma A2_2_12Law_sound (u : Shape) :
    (A2_2_12Law u).Encloses (stageALaw (shape 2 2 12) u : ℝ) := by
  by_cases hu : u ∈ below (shape 2 2 12)
  · have h := contains_sound (Ball.mul_sound (A2_2_12Raw_sound u hu)
      (Ball.inv_sound A2_2_12Den_sound A2_2_12Den_positive)) (A2_2_12Law_check u hu)
    simpa only [A2_2_12Law, hu, ite_true, if_true, stageALaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [A2_2_12Law, hu, ite_false, if_false, stageALaw, splitLaw, Rat.cast_zero]
    simpa only [Rat.cast_zero] using Ball.exact_sound 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitA2_3_11
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
lemma A2_3_11_below : below (shape 2 3 11) = [
  (shape 0 0 8),
  (shape 0 1 7),
  (shape 0 2 6),
  (shape 0 3 5),
  (shape 1 0 7),
  (shape 1 1 6),
  (shape 1 2 5),
  (shape 1 3 4),
  (shape 2 0 6),
  (shape 2 1 5),
  (shape 2 2 4),
  (shape 2 3 3)] := by decide +kernel
lemma A2_3_11Raw_0_0_8 : (A2_3_11Raw (shape 0 0 8)).Encloses (splitWeight positiveInitial tableP (shape 2 3 11) (shape 0 0 8) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 3 11) (shape 0 0 8)
    (-3270) (-6376) (-53221) w184 w157 w33
    (by decide +kernel) w184_sound w157_sound w33_sound) (by decide +kernel)
lemma A2_3_11Raw_0_1_7 : (A2_3_11Raw (shape 0 1 7)).Encloses (splitWeight positiveInitial tableP (shape 2 3 11) (shape 0 1 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 3 11) (shape 0 1 7)
    (-3270) (0) (-15352) w184 w195 w112
    (by decide +kernel) w184_sound w195_sound w112_sound) (by decide +kernel)
lemma A2_3_11Raw_0_2_6 : (A2_3_11Raw (shape 0 2 6)).Encloses (splitWeight positiveInitial tableP (shape 2 3 11) (shape 0 2 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 3 11) (shape 0 2 6)
    (-3270) (0) (0) w184 w195 w195
    (by decide +kernel) w184_sound w195_sound w195_sound) (by decide +kernel)
lemma A2_3_11Raw_0_3_5 : (A2_3_11Raw (shape 0 3 5)).Encloses (splitWeight positiveInitial tableP (shape 2 3 11) (shape 0 3 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 3 11) (shape 0 3 5)
    (-3270) (-6376) (0) w184 w157 w195
    (by decide +kernel) w184_sound w157_sound w195_sound) (by decide +kernel)
lemma A2_3_11Raw_1_0_7 : (A2_3_11Raw (shape 1 0 7)).Encloses (splitWeight positiveInitial tableP (shape 2 3 11) (shape 1 0 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 3 11) (shape 1 0 7)
    (0) (-6376) (-15352) w195 w157 w112
    (by decide +kernel) w195_sound w157_sound w112_sound) (by decide +kernel)
lemma A2_3_11Raw_1_1_6 : (A2_3_11Raw (shape 1 1 6)).Encloses (splitWeight positiveInitial tableP (shape 2 3 11) (shape 1 1 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 3 11) (shape 1 1 6)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A2_3_11Raw_1_2_5 : (A2_3_11Raw (shape 1 2 5)).Encloses (splitWeight positiveInitial tableP (shape 2 3 11) (shape 1 2 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 3 11) (shape 1 2 5)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A2_3_11Raw_1_3_4 : (A2_3_11Raw (shape 1 3 4)).Encloses (splitWeight positiveInitial tableP (shape 2 3 11) (shape 1 3 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 3 11) (shape 1 3 4)
    (0) (-6376) (-15352) w195 w157 w112
    (by decide +kernel) w195_sound w157_sound w112_sound) (by decide +kernel)
lemma A2_3_11Raw_2_0_6 : (A2_3_11Raw (shape 2 0 6)).Encloses (splitWeight positiveInitial tableP (shape 2 3 11) (shape 2 0 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 3 11) (shape 2 0 6)
    (-3270) (-6376) (0) w184 w157 w195
    (by decide +kernel) w184_sound w157_sound w195_sound) (by decide +kernel)
lemma A2_3_11Raw_2_1_5 : (A2_3_11Raw (shape 2 1 5)).Encloses (splitWeight positiveInitial tableP (shape 2 3 11) (shape 2 1 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 3 11) (shape 2 1 5)
    (-3270) (0) (0) w184 w195 w195
    (by decide +kernel) w184_sound w195_sound w195_sound) (by decide +kernel)
lemma A2_3_11Raw_2_2_4 : (A2_3_11Raw (shape 2 2 4)).Encloses (splitWeight positiveInitial tableP (shape 2 3 11) (shape 2 2 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 3 11) (shape 2 2 4)
    (-3270) (0) (-15352) w184 w195 w112
    (by decide +kernel) w184_sound w195_sound w112_sound) (by decide +kernel)
lemma A2_3_11Raw_2_3_3 : (A2_3_11Raw (shape 2 3 3)).Encloses (splitWeight positiveInitial tableP (shape 2 3 11) (shape 2 3 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 3 11) (shape 2 3 3)
    (-3270) (-6376) (-53221) w184 w157 w33
    (by decide +kernel) w184_sound w157_sound w33_sound) (by decide +kernel)
lemma A2_3_11Raw_sound (u : Shape) (hu : u ∈ below (shape 2 3 11)) :
    (A2_3_11Raw u).Encloses (splitWeight positiveInitial tableP (shape 2 3 11) u : ℝ) := by
  rw [A2_3_11_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A2_3_11Raw_0_0_8
  · exact A2_3_11Raw_0_1_7
  · exact A2_3_11Raw_0_2_6
  · exact A2_3_11Raw_0_3_5
  · exact A2_3_11Raw_1_0_7
  · exact A2_3_11Raw_1_1_6
  · exact A2_3_11Raw_1_2_5
  · exact A2_3_11Raw_1_3_4
  · exact A2_3_11Raw_2_0_6
  · exact A2_3_11Raw_2_1_5
  · exact A2_3_11Raw_2_2_4
  · exact A2_3_11Raw_2_3_3
lemma A2_3_11Den_sound : A2_3_11Den.Encloses (((below (shape 2 3 11)).map (splitWeight positiveInitial tableP (shape 2 3 11))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (below (shape 2 3 11)) A2_3_11Raw (splitWeight positiveInitial tableP (shape 2 3 11)) A2_3_11Raw_sound) (by decide +kernel)
lemma A2_3_11Den_positive : 0 < A2_3_11Den.lower := by decide +kernel
lemma A2_3_11Law_check_0_0_8 : contains (.mul (A2_3_11Raw (shape 0 0 8)) (.inv A2_3_11Den)) (A2_3_11Table (shape 0 0 8)) = true := by decide +kernel
lemma A2_3_11Law_check_0_1_7 : contains (.mul (A2_3_11Raw (shape 0 1 7)) (.inv A2_3_11Den)) (A2_3_11Table (shape 0 1 7)) = true := by decide +kernel
lemma A2_3_11Law_check_0_2_6 : contains (.mul (A2_3_11Raw (shape 0 2 6)) (.inv A2_3_11Den)) (A2_3_11Table (shape 0 2 6)) = true := by decide +kernel
lemma A2_3_11Law_check_0_3_5 : contains (.mul (A2_3_11Raw (shape 0 3 5)) (.inv A2_3_11Den)) (A2_3_11Table (shape 0 3 5)) = true := by decide +kernel
lemma A2_3_11Law_check_1_0_7 : contains (.mul (A2_3_11Raw (shape 1 0 7)) (.inv A2_3_11Den)) (A2_3_11Table (shape 1 0 7)) = true := by decide +kernel
lemma A2_3_11Law_check_1_1_6 : contains (.mul (A2_3_11Raw (shape 1 1 6)) (.inv A2_3_11Den)) (A2_3_11Table (shape 1 1 6)) = true := by decide +kernel
lemma A2_3_11Law_check_1_2_5 : contains (.mul (A2_3_11Raw (shape 1 2 5)) (.inv A2_3_11Den)) (A2_3_11Table (shape 1 2 5)) = true := by decide +kernel
lemma A2_3_11Law_check_1_3_4 : contains (.mul (A2_3_11Raw (shape 1 3 4)) (.inv A2_3_11Den)) (A2_3_11Table (shape 1 3 4)) = true := by decide +kernel
lemma A2_3_11Law_check_2_0_6 : contains (.mul (A2_3_11Raw (shape 2 0 6)) (.inv A2_3_11Den)) (A2_3_11Table (shape 2 0 6)) = true := by decide +kernel
lemma A2_3_11Law_check_2_1_5 : contains (.mul (A2_3_11Raw (shape 2 1 5)) (.inv A2_3_11Den)) (A2_3_11Table (shape 2 1 5)) = true := by decide +kernel
lemma A2_3_11Law_check_2_2_4 : contains (.mul (A2_3_11Raw (shape 2 2 4)) (.inv A2_3_11Den)) (A2_3_11Table (shape 2 2 4)) = true := by decide +kernel
lemma A2_3_11Law_check_2_3_3 : contains (.mul (A2_3_11Raw (shape 2 3 3)) (.inv A2_3_11Den)) (A2_3_11Table (shape 2 3 3)) = true := by decide +kernel
lemma A2_3_11Law_check (u : Shape) (hu : u ∈ below (shape 2 3 11)) :
    contains (.mul (A2_3_11Raw u) (.inv A2_3_11Den)) (A2_3_11Table u) = true := by
  rw [A2_3_11_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A2_3_11Law_check_0_0_8
  · exact A2_3_11Law_check_0_1_7
  · exact A2_3_11Law_check_0_2_6
  · exact A2_3_11Law_check_0_3_5
  · exact A2_3_11Law_check_1_0_7
  · exact A2_3_11Law_check_1_1_6
  · exact A2_3_11Law_check_1_2_5
  · exact A2_3_11Law_check_1_3_4
  · exact A2_3_11Law_check_2_0_6
  · exact A2_3_11Law_check_2_1_5
  · exact A2_3_11Law_check_2_2_4
  · exact A2_3_11Law_check_2_3_3
lemma A2_3_11Law_sound (u : Shape) :
    (A2_3_11Law u).Encloses (stageALaw (shape 2 3 11) u : ℝ) := by
  by_cases hu : u ∈ below (shape 2 3 11)
  · have h := contains_sound (Ball.mul_sound (A2_3_11Raw_sound u hu)
      (Ball.inv_sound A2_3_11Den_sound A2_3_11Den_positive)) (A2_3_11Law_check u hu)
    simpa only [A2_3_11Law, hu, ite_true, if_true, stageALaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [A2_3_11Law, hu, ite_false, if_false, stageALaw, splitLaw, Rat.cast_zero]
    simpa only [Rat.cast_zero] using Ball.exact_sound 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitA2_5_9
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
lemma A2_5_9_below : below (shape 2 5 9) = [
  (shape 0 0 8),
  (shape 0 1 7),
  (shape 0 2 6),
  (shape 0 3 5),
  (shape 0 4 4),
  (shape 0 5 3),
  (shape 1 0 7),
  (shape 1 1 6),
  (shape 1 2 5),
  (shape 1 3 4),
  (shape 1 4 3),
  (shape 1 5 2),
  (shape 2 0 6),
  (shape 2 1 5),
  (shape 2 2 4),
  (shape 2 3 3),
  (shape 2 4 2),
  (shape 2 5 1)] := by decide +kernel
lemma A2_5_9Raw_0_0_8 : (A2_5_9Raw (shape 0 0 8)).Encloses (splitWeight positiveInitial tableP (shape 2 5 9) (shape 0 0 8) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 5 9) (shape 0 0 8)
    (-3578) (-24599) (-92989) w181 w82 w6
    (by decide +kernel) w181_sound w82_sound w6_sound) (by decide +kernel)
lemma A2_5_9Raw_0_1_7 : (A2_5_9Raw (shape 0 1 7)).Encloses (splitWeight positiveInitial tableP (shape 2 5 9) (shape 0 1 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 5 9) (shape 0 1 7)
    (-3578) (-8700) (-46655) w181 w137 w39
    (by decide +kernel) w181_sound w137_sound w39_sound) (by decide +kernel)
lemma A2_5_9Raw_0_2_6 : (A2_5_9Raw (shape 0 2 6)).Encloses (splitWeight positiveInitial tableP (shape 2 5 9) (shape 0 2 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 5 9) (shape 0 2 6)
    (-3578) (0) (-16926) w181 w195 w101
    (by decide +kernel) w181_sound w195_sound w101_sound) (by decide +kernel)
lemma A2_5_9Raw_0_3_5 : (A2_5_9Raw (shape 0 3 5)).Encloses (splitWeight positiveInitial tableP (shape 2 5 9) (shape 0 3 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 5 9) (shape 0 3 5)
    (-3578) (0) (0) w181 w195 w195
    (by decide +kernel) w181_sound w195_sound w195_sound) (by decide +kernel)
lemma A2_5_9Raw_0_4_4 : (A2_5_9Raw (shape 0 4 4)).Encloses (splitWeight positiveInitial tableP (shape 2 5 9) (shape 0 4 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 5 9) (shape 0 4 4)
    (-3578) (-8700) (0) w181 w137 w195
    (by decide +kernel) w181_sound w137_sound w195_sound) (by decide +kernel)
lemma A2_5_9Raw_0_5_3 : (A2_5_9Raw (shape 0 5 3)).Encloses (splitWeight positiveInitial tableP (shape 2 5 9) (shape 0 5 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 5 9) (shape 0 5 3)
    (-3578) (-24599) (-16926) w181 w82 w101
    (by decide +kernel) w181_sound w82_sound w101_sound) (by decide +kernel)
lemma A2_5_9Raw_1_0_7 : (A2_5_9Raw (shape 1 0 7)).Encloses (splitWeight positiveInitial tableP (shape 2 5 9) (shape 1 0 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 5 9) (shape 1 0 7)
    (0) (-24599) (-46655) w195 w82 w39
    (by decide +kernel) w195_sound w82_sound w39_sound) (by decide +kernel)
lemma A2_5_9Raw_1_1_6 : (A2_5_9Raw (shape 1 1 6)).Encloses (splitWeight positiveInitial tableP (shape 2 5 9) (shape 1 1 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 5 9) (shape 1 1 6)
    (0) (-8700) (-16926) w195 w137 w101
    (by decide +kernel) w195_sound w137_sound w101_sound) (by decide +kernel)
lemma A2_5_9Raw_1_2_5 : (A2_5_9Raw (shape 1 2 5)).Encloses (splitWeight positiveInitial tableP (shape 2 5 9) (shape 1 2 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 5 9) (shape 1 2 5)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A2_5_9Raw_1_3_4 : (A2_5_9Raw (shape 1 3 4)).Encloses (splitWeight positiveInitial tableP (shape 2 5 9) (shape 1 3 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 5 9) (shape 1 3 4)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A2_5_9Raw_1_4_3 : (A2_5_9Raw (shape 1 4 3)).Encloses (splitWeight positiveInitial tableP (shape 2 5 9) (shape 1 4 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 5 9) (shape 1 4 3)
    (0) (-8700) (-16926) w195 w137 w101
    (by decide +kernel) w195_sound w137_sound w101_sound) (by decide +kernel)
lemma A2_5_9Raw_1_5_2 : (A2_5_9Raw (shape 1 5 2)).Encloses (splitWeight positiveInitial tableP (shape 2 5 9) (shape 1 5 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 5 9) (shape 1 5 2)
    (0) (-24599) (-46655) w195 w82 w39
    (by decide +kernel) w195_sound w82_sound w39_sound) (by decide +kernel)
lemma A2_5_9Raw_2_0_6 : (A2_5_9Raw (shape 2 0 6)).Encloses (splitWeight positiveInitial tableP (shape 2 5 9) (shape 2 0 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 5 9) (shape 2 0 6)
    (-3578) (-24599) (-16926) w181 w82 w101
    (by decide +kernel) w181_sound w82_sound w101_sound) (by decide +kernel)
lemma A2_5_9Raw_2_1_5 : (A2_5_9Raw (shape 2 1 5)).Encloses (splitWeight positiveInitial tableP (shape 2 5 9) (shape 2 1 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 5 9) (shape 2 1 5)
    (-3578) (-8700) (0) w181 w137 w195
    (by decide +kernel) w181_sound w137_sound w195_sound) (by decide +kernel)
lemma A2_5_9Raw_2_2_4 : (A2_5_9Raw (shape 2 2 4)).Encloses (splitWeight positiveInitial tableP (shape 2 5 9) (shape 2 2 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 5 9) (shape 2 2 4)
    (-3578) (0) (0) w181 w195 w195
    (by decide +kernel) w181_sound w195_sound w195_sound) (by decide +kernel)
lemma A2_5_9Raw_2_3_3 : (A2_5_9Raw (shape 2 3 3)).Encloses (splitWeight positiveInitial tableP (shape 2 5 9) (shape 2 3 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 5 9) (shape 2 3 3)
    (-3578) (0) (-16926) w181 w195 w101
    (by decide +kernel) w181_sound w195_sound w101_sound) (by decide +kernel)
lemma A2_5_9Raw_2_4_2 : (A2_5_9Raw (shape 2 4 2)).Encloses (splitWeight positiveInitial tableP (shape 2 5 9) (shape 2 4 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 5 9) (shape 2 4 2)
    (-3578) (-8700) (-46655) w181 w137 w39
    (by decide +kernel) w181_sound w137_sound w39_sound) (by decide +kernel)
lemma A2_5_9Raw_2_5_1 : (A2_5_9Raw (shape 2 5 1)).Encloses (splitWeight positiveInitial tableP (shape 2 5 9) (shape 2 5 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 5 9) (shape 2 5 1)
    (-3578) (-24599) (-92989) w181 w82 w6
    (by decide +kernel) w181_sound w82_sound w6_sound) (by decide +kernel)
lemma A2_5_9Raw_sound (u : Shape) (hu : u ∈ below (shape 2 5 9)) :
    (A2_5_9Raw u).Encloses (splitWeight positiveInitial tableP (shape 2 5 9) u : ℝ) := by
  rw [A2_5_9_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A2_5_9Raw_0_0_8
  · exact A2_5_9Raw_0_1_7
  · exact A2_5_9Raw_0_2_6
  · exact A2_5_9Raw_0_3_5
  · exact A2_5_9Raw_0_4_4
  · exact A2_5_9Raw_0_5_3
  · exact A2_5_9Raw_1_0_7
  · exact A2_5_9Raw_1_1_6
  · exact A2_5_9Raw_1_2_5
  · exact A2_5_9Raw_1_3_4
  · exact A2_5_9Raw_1_4_3
  · exact A2_5_9Raw_1_5_2
  · exact A2_5_9Raw_2_0_6
  · exact A2_5_9Raw_2_1_5
  · exact A2_5_9Raw_2_2_4
  · exact A2_5_9Raw_2_3_3
  · exact A2_5_9Raw_2_4_2
  · exact A2_5_9Raw_2_5_1
lemma A2_5_9Den_sound : A2_5_9Den.Encloses (((below (shape 2 5 9)).map (splitWeight positiveInitial tableP (shape 2 5 9))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (below (shape 2 5 9)) A2_5_9Raw (splitWeight positiveInitial tableP (shape 2 5 9)) A2_5_9Raw_sound) (by decide +kernel)
lemma A2_5_9Den_positive : 0 < A2_5_9Den.lower := by decide +kernel
lemma A2_5_9Law_check_0_0_8 : contains (.mul (A2_5_9Raw (shape 0 0 8)) (.inv A2_5_9Den)) (A2_5_9Table (shape 0 0 8)) = true := by decide +kernel
lemma A2_5_9Law_check_0_1_7 : contains (.mul (A2_5_9Raw (shape 0 1 7)) (.inv A2_5_9Den)) (A2_5_9Table (shape 0 1 7)) = true := by decide +kernel
lemma A2_5_9Law_check_0_2_6 : contains (.mul (A2_5_9Raw (shape 0 2 6)) (.inv A2_5_9Den)) (A2_5_9Table (shape 0 2 6)) = true := by decide +kernel
lemma A2_5_9Law_check_0_3_5 : contains (.mul (A2_5_9Raw (shape 0 3 5)) (.inv A2_5_9Den)) (A2_5_9Table (shape 0 3 5)) = true := by decide +kernel
lemma A2_5_9Law_check_0_4_4 : contains (.mul (A2_5_9Raw (shape 0 4 4)) (.inv A2_5_9Den)) (A2_5_9Table (shape 0 4 4)) = true := by decide +kernel
lemma A2_5_9Law_check_0_5_3 : contains (.mul (A2_5_9Raw (shape 0 5 3)) (.inv A2_5_9Den)) (A2_5_9Table (shape 0 5 3)) = true := by decide +kernel
lemma A2_5_9Law_check_1_0_7 : contains (.mul (A2_5_9Raw (shape 1 0 7)) (.inv A2_5_9Den)) (A2_5_9Table (shape 1 0 7)) = true := by decide +kernel
lemma A2_5_9Law_check_1_1_6 : contains (.mul (A2_5_9Raw (shape 1 1 6)) (.inv A2_5_9Den)) (A2_5_9Table (shape 1 1 6)) = true := by decide +kernel
lemma A2_5_9Law_check_1_2_5 : contains (.mul (A2_5_9Raw (shape 1 2 5)) (.inv A2_5_9Den)) (A2_5_9Table (shape 1 2 5)) = true := by decide +kernel
lemma A2_5_9Law_check_1_3_4 : contains (.mul (A2_5_9Raw (shape 1 3 4)) (.inv A2_5_9Den)) (A2_5_9Table (shape 1 3 4)) = true := by decide +kernel
lemma A2_5_9Law_check_1_4_3 : contains (.mul (A2_5_9Raw (shape 1 4 3)) (.inv A2_5_9Den)) (A2_5_9Table (shape 1 4 3)) = true := by decide +kernel
lemma A2_5_9Law_check_1_5_2 : contains (.mul (A2_5_9Raw (shape 1 5 2)) (.inv A2_5_9Den)) (A2_5_9Table (shape 1 5 2)) = true := by decide +kernel
lemma A2_5_9Law_check_2_0_6 : contains (.mul (A2_5_9Raw (shape 2 0 6)) (.inv A2_5_9Den)) (A2_5_9Table (shape 2 0 6)) = true := by decide +kernel
lemma A2_5_9Law_check_2_1_5 : contains (.mul (A2_5_9Raw (shape 2 1 5)) (.inv A2_5_9Den)) (A2_5_9Table (shape 2 1 5)) = true := by decide +kernel
lemma A2_5_9Law_check_2_2_4 : contains (.mul (A2_5_9Raw (shape 2 2 4)) (.inv A2_5_9Den)) (A2_5_9Table (shape 2 2 4)) = true := by decide +kernel
lemma A2_5_9Law_check_2_3_3 : contains (.mul (A2_5_9Raw (shape 2 3 3)) (.inv A2_5_9Den)) (A2_5_9Table (shape 2 3 3)) = true := by decide +kernel
lemma A2_5_9Law_check_2_4_2 : contains (.mul (A2_5_9Raw (shape 2 4 2)) (.inv A2_5_9Den)) (A2_5_9Table (shape 2 4 2)) = true := by decide +kernel
lemma A2_5_9Law_check_2_5_1 : contains (.mul (A2_5_9Raw (shape 2 5 1)) (.inv A2_5_9Den)) (A2_5_9Table (shape 2 5 1)) = true := by decide +kernel
lemma A2_5_9Law_check (u : Shape) (hu : u ∈ below (shape 2 5 9)) :
    contains (.mul (A2_5_9Raw u) (.inv A2_5_9Den)) (A2_5_9Table u) = true := by
  rw [A2_5_9_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A2_5_9Law_check_0_0_8
  · exact A2_5_9Law_check_0_1_7
  · exact A2_5_9Law_check_0_2_6
  · exact A2_5_9Law_check_0_3_5
  · exact A2_5_9Law_check_0_4_4
  · exact A2_5_9Law_check_0_5_3
  · exact A2_5_9Law_check_1_0_7
  · exact A2_5_9Law_check_1_1_6
  · exact A2_5_9Law_check_1_2_5
  · exact A2_5_9Law_check_1_3_4
  · exact A2_5_9Law_check_1_4_3
  · exact A2_5_9Law_check_1_5_2
  · exact A2_5_9Law_check_2_0_6
  · exact A2_5_9Law_check_2_1_5
  · exact A2_5_9Law_check_2_2_4
  · exact A2_5_9Law_check_2_3_3
  · exact A2_5_9Law_check_2_4_2
  · exact A2_5_9Law_check_2_5_1
lemma A2_5_9Law_sound (u : Shape) :
    (A2_5_9Law u).Encloses (stageALaw (shape 2 5 9) u : ℝ) := by
  by_cases hu : u ∈ below (shape 2 5 9)
  · have h := contains_sound (Ball.mul_sound (A2_5_9Raw_sound u hu)
      (Ball.inv_sound A2_5_9Den_sound A2_5_9Den_positive)) (A2_5_9Law_check u hu)
    simpa only [A2_5_9Law, hu, ite_true, if_true, stageALaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [A2_5_9Law, hu, ite_false, if_false, stageALaw, splitLaw, Rat.cast_zero]
    simpa only [Rat.cast_zero] using Ball.exact_sound 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitA3_4_9
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
lemma A3_4_9_below : below (shape 3 4 9) = [
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
  (shape 3 4 1)] := by decide +kernel
lemma A3_4_9Raw_0_0_8 : (A3_4_9Raw (shape 0 0 8)).Encloses (splitWeight positiveInitial tableP (shape 3 4 9) (shape 0 0 8) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 4 9) (shape 0 0 8)
    (-7447) (-17336) (-96770) w144 w97 w3
    (by decide +kernel) w144_sound w97_sound w3_sound) (by decide +kernel)
lemma A3_4_9Raw_0_1_7 : (A3_4_9Raw (shape 0 1 7)).Encloses (splitWeight positiveInitial tableP (shape 3 4 9) (shape 0 1 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 4 9) (shape 0 1 7)
    (-7447) (-4721) (-49297) w144 w173 w36
    (by decide +kernel) w144_sound w173_sound w36_sound) (by decide +kernel)
lemma A3_4_9Raw_0_2_6 : (A3_4_9Raw (shape 0 2 6)).Encloses (splitWeight positiveInitial tableP (shape 3 4 9) (shape 0 2 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 4 9) (shape 0 2 6)
    (-7447) (0) (-17874) w144 w195 w95
    (by decide +kernel) w144_sound w195_sound w95_sound) (by decide +kernel)
lemma A3_4_9Raw_0_3_5 : (A3_4_9Raw (shape 0 3 5)).Encloses (splitWeight positiveInitial tableP (shape 3 4 9) (shape 0 3 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 4 9) (shape 0 3 5)
    (-7447) (-4721) (0) w144 w173 w195
    (by decide +kernel) w144_sound w173_sound w195_sound) (by decide +kernel)
lemma A3_4_9Raw_0_4_4 : (A3_4_9Raw (shape 0 4 4)).Encloses (splitWeight positiveInitial tableP (shape 3 4 9) (shape 0 4 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 4 9) (shape 0 4 4)
    (-7447) (-17336) (0) w144 w97 w195
    (by decide +kernel) w144_sound w97_sound w195_sound) (by decide +kernel)
lemma A3_4_9Raw_1_0_7 : (A3_4_9Raw (shape 1 0 7)).Encloses (splitWeight positiveInitial tableP (shape 3 4 9) (shape 1 0 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 4 9) (shape 1 0 7)
    (0) (-17336) (-49297) w195 w97 w36
    (by decide +kernel) w195_sound w97_sound w36_sound) (by decide +kernel)
lemma A3_4_9Raw_1_1_6 : (A3_4_9Raw (shape 1 1 6)).Encloses (splitWeight positiveInitial tableP (shape 3 4 9) (shape 1 1 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 4 9) (shape 1 1 6)
    (0) (-4721) (-17874) w195 w173 w95
    (by decide +kernel) w195_sound w173_sound w95_sound) (by decide +kernel)
lemma A3_4_9Raw_1_2_5 : (A3_4_9Raw (shape 1 2 5)).Encloses (splitWeight positiveInitial tableP (shape 3 4 9) (shape 1 2 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 4 9) (shape 1 2 5)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A3_4_9Raw_1_3_4 : (A3_4_9Raw (shape 1 3 4)).Encloses (splitWeight positiveInitial tableP (shape 3 4 9) (shape 1 3 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 4 9) (shape 1 3 4)
    (0) (-4721) (0) w195 w173 w195
    (by decide +kernel) w195_sound w173_sound w195_sound) (by decide +kernel)
lemma A3_4_9Raw_1_4_3 : (A3_4_9Raw (shape 1 4 3)).Encloses (splitWeight positiveInitial tableP (shape 3 4 9) (shape 1 4 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 4 9) (shape 1 4 3)
    (0) (-17336) (-17874) w195 w97 w95
    (by decide +kernel) w195_sound w97_sound w95_sound) (by decide +kernel)
lemma A3_4_9Raw_2_0_6 : (A3_4_9Raw (shape 2 0 6)).Encloses (splitWeight positiveInitial tableP (shape 3 4 9) (shape 2 0 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 4 9) (shape 2 0 6)
    (0) (-17336) (-17874) w195 w97 w95
    (by decide +kernel) w195_sound w97_sound w95_sound) (by decide +kernel)
lemma A3_4_9Raw_2_1_5 : (A3_4_9Raw (shape 2 1 5)).Encloses (splitWeight positiveInitial tableP (shape 3 4 9) (shape 2 1 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 4 9) (shape 2 1 5)
    (0) (-4721) (0) w195 w173 w195
    (by decide +kernel) w195_sound w173_sound w195_sound) (by decide +kernel)
lemma A3_4_9Raw_2_2_4 : (A3_4_9Raw (shape 2 2 4)).Encloses (splitWeight positiveInitial tableP (shape 3 4 9) (shape 2 2 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 4 9) (shape 2 2 4)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A3_4_9Raw_2_3_3 : (A3_4_9Raw (shape 2 3 3)).Encloses (splitWeight positiveInitial tableP (shape 3 4 9) (shape 2 3 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 4 9) (shape 2 3 3)
    (0) (-4721) (-17874) w195 w173 w95
    (by decide +kernel) w195_sound w173_sound w95_sound) (by decide +kernel)
lemma A3_4_9Raw_2_4_2 : (A3_4_9Raw (shape 2 4 2)).Encloses (splitWeight positiveInitial tableP (shape 3 4 9) (shape 2 4 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 4 9) (shape 2 4 2)
    (0) (-17336) (-49297) w195 w97 w36
    (by decide +kernel) w195_sound w97_sound w36_sound) (by decide +kernel)
lemma A3_4_9Raw_3_0_5 : (A3_4_9Raw (shape 3 0 5)).Encloses (splitWeight positiveInitial tableP (shape 3 4 9) (shape 3 0 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 4 9) (shape 3 0 5)
    (-7447) (-17336) (0) w144 w97 w195
    (by decide +kernel) w144_sound w97_sound w195_sound) (by decide +kernel)
lemma A3_4_9Raw_3_1_4 : (A3_4_9Raw (shape 3 1 4)).Encloses (splitWeight positiveInitial tableP (shape 3 4 9) (shape 3 1 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 4 9) (shape 3 1 4)
    (-7447) (-4721) (0) w144 w173 w195
    (by decide +kernel) w144_sound w173_sound w195_sound) (by decide +kernel)
lemma A3_4_9Raw_3_2_3 : (A3_4_9Raw (shape 3 2 3)).Encloses (splitWeight positiveInitial tableP (shape 3 4 9) (shape 3 2 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 4 9) (shape 3 2 3)
    (-7447) (0) (-17874) w144 w195 w95
    (by decide +kernel) w144_sound w195_sound w95_sound) (by decide +kernel)
lemma A3_4_9Raw_3_3_2 : (A3_4_9Raw (shape 3 3 2)).Encloses (splitWeight positiveInitial tableP (shape 3 4 9) (shape 3 3 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 4 9) (shape 3 3 2)
    (-7447) (-4721) (-49297) w144 w173 w36
    (by decide +kernel) w144_sound w173_sound w36_sound) (by decide +kernel)
lemma A3_4_9Raw_3_4_1 : (A3_4_9Raw (shape 3 4 1)).Encloses (splitWeight positiveInitial tableP (shape 3 4 9) (shape 3 4 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 4 9) (shape 3 4 1)
    (-7447) (-17336) (-96770) w144 w97 w3
    (by decide +kernel) w144_sound w97_sound w3_sound) (by decide +kernel)
lemma A3_4_9Raw_sound (u : Shape) (hu : u ∈ below (shape 3 4 9)) :
    (A3_4_9Raw u).Encloses (splitWeight positiveInitial tableP (shape 3 4 9) u : ℝ) := by
  rw [A3_4_9_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A3_4_9Raw_0_0_8
  · exact A3_4_9Raw_0_1_7
  · exact A3_4_9Raw_0_2_6
  · exact A3_4_9Raw_0_3_5
  · exact A3_4_9Raw_0_4_4
  · exact A3_4_9Raw_1_0_7
  · exact A3_4_9Raw_1_1_6
  · exact A3_4_9Raw_1_2_5
  · exact A3_4_9Raw_1_3_4
  · exact A3_4_9Raw_1_4_3
  · exact A3_4_9Raw_2_0_6
  · exact A3_4_9Raw_2_1_5
  · exact A3_4_9Raw_2_2_4
  · exact A3_4_9Raw_2_3_3
  · exact A3_4_9Raw_2_4_2
  · exact A3_4_9Raw_3_0_5
  · exact A3_4_9Raw_3_1_4
  · exact A3_4_9Raw_3_2_3
  · exact A3_4_9Raw_3_3_2
  · exact A3_4_9Raw_3_4_1
lemma A3_4_9Den_sound : A3_4_9Den.Encloses (((below (shape 3 4 9)).map (splitWeight positiveInitial tableP (shape 3 4 9))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (below (shape 3 4 9)) A3_4_9Raw (splitWeight positiveInitial tableP (shape 3 4 9)) A3_4_9Raw_sound) (by decide +kernel)
lemma A3_4_9Den_positive : 0 < A3_4_9Den.lower := by decide +kernel
lemma A3_4_9Law_check_0_0_8 : contains (.mul (A3_4_9Raw (shape 0 0 8)) (.inv A3_4_9Den)) (A3_4_9Table (shape 0 0 8)) = true := by decide +kernel
lemma A3_4_9Law_check_0_1_7 : contains (.mul (A3_4_9Raw (shape 0 1 7)) (.inv A3_4_9Den)) (A3_4_9Table (shape 0 1 7)) = true := by decide +kernel
lemma A3_4_9Law_check_0_2_6 : contains (.mul (A3_4_9Raw (shape 0 2 6)) (.inv A3_4_9Den)) (A3_4_9Table (shape 0 2 6)) = true := by decide +kernel
lemma A3_4_9Law_check_0_3_5 : contains (.mul (A3_4_9Raw (shape 0 3 5)) (.inv A3_4_9Den)) (A3_4_9Table (shape 0 3 5)) = true := by decide +kernel
lemma A3_4_9Law_check_0_4_4 : contains (.mul (A3_4_9Raw (shape 0 4 4)) (.inv A3_4_9Den)) (A3_4_9Table (shape 0 4 4)) = true := by decide +kernel
lemma A3_4_9Law_check_1_0_7 : contains (.mul (A3_4_9Raw (shape 1 0 7)) (.inv A3_4_9Den)) (A3_4_9Table (shape 1 0 7)) = true := by decide +kernel
lemma A3_4_9Law_check_1_1_6 : contains (.mul (A3_4_9Raw (shape 1 1 6)) (.inv A3_4_9Den)) (A3_4_9Table (shape 1 1 6)) = true := by decide +kernel
lemma A3_4_9Law_check_1_2_5 : contains (.mul (A3_4_9Raw (shape 1 2 5)) (.inv A3_4_9Den)) (A3_4_9Table (shape 1 2 5)) = true := by decide +kernel
lemma A3_4_9Law_check_1_3_4 : contains (.mul (A3_4_9Raw (shape 1 3 4)) (.inv A3_4_9Den)) (A3_4_9Table (shape 1 3 4)) = true := by decide +kernel
lemma A3_4_9Law_check_1_4_3 : contains (.mul (A3_4_9Raw (shape 1 4 3)) (.inv A3_4_9Den)) (A3_4_9Table (shape 1 4 3)) = true := by decide +kernel
lemma A3_4_9Law_check_2_0_6 : contains (.mul (A3_4_9Raw (shape 2 0 6)) (.inv A3_4_9Den)) (A3_4_9Table (shape 2 0 6)) = true := by decide +kernel
lemma A3_4_9Law_check_2_1_5 : contains (.mul (A3_4_9Raw (shape 2 1 5)) (.inv A3_4_9Den)) (A3_4_9Table (shape 2 1 5)) = true := by decide +kernel
lemma A3_4_9Law_check_2_2_4 : contains (.mul (A3_4_9Raw (shape 2 2 4)) (.inv A3_4_9Den)) (A3_4_9Table (shape 2 2 4)) = true := by decide +kernel
lemma A3_4_9Law_check_2_3_3 : contains (.mul (A3_4_9Raw (shape 2 3 3)) (.inv A3_4_9Den)) (A3_4_9Table (shape 2 3 3)) = true := by decide +kernel
lemma A3_4_9Law_check_2_4_2 : contains (.mul (A3_4_9Raw (shape 2 4 2)) (.inv A3_4_9Den)) (A3_4_9Table (shape 2 4 2)) = true := by decide +kernel
lemma A3_4_9Law_check_3_0_5 : contains (.mul (A3_4_9Raw (shape 3 0 5)) (.inv A3_4_9Den)) (A3_4_9Table (shape 3 0 5)) = true := by decide +kernel
lemma A3_4_9Law_check_3_1_4 : contains (.mul (A3_4_9Raw (shape 3 1 4)) (.inv A3_4_9Den)) (A3_4_9Table (shape 3 1 4)) = true := by decide +kernel
lemma A3_4_9Law_check_3_2_3 : contains (.mul (A3_4_9Raw (shape 3 2 3)) (.inv A3_4_9Den)) (A3_4_9Table (shape 3 2 3)) = true := by decide +kernel
lemma A3_4_9Law_check_3_3_2 : contains (.mul (A3_4_9Raw (shape 3 3 2)) (.inv A3_4_9Den)) (A3_4_9Table (shape 3 3 2)) = true := by decide +kernel
lemma A3_4_9Law_check_3_4_1 : contains (.mul (A3_4_9Raw (shape 3 4 1)) (.inv A3_4_9Den)) (A3_4_9Table (shape 3 4 1)) = true := by decide +kernel
lemma A3_4_9Law_check (u : Shape) (hu : u ∈ below (shape 3 4 9)) :
    contains (.mul (A3_4_9Raw u) (.inv A3_4_9Den)) (A3_4_9Table u) = true := by
  rw [A3_4_9_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A3_4_9Law_check_0_0_8
  · exact A3_4_9Law_check_0_1_7
  · exact A3_4_9Law_check_0_2_6
  · exact A3_4_9Law_check_0_3_5
  · exact A3_4_9Law_check_0_4_4
  · exact A3_4_9Law_check_1_0_7
  · exact A3_4_9Law_check_1_1_6
  · exact A3_4_9Law_check_1_2_5
  · exact A3_4_9Law_check_1_3_4
  · exact A3_4_9Law_check_1_4_3
  · exact A3_4_9Law_check_2_0_6
  · exact A3_4_9Law_check_2_1_5
  · exact A3_4_9Law_check_2_2_4
  · exact A3_4_9Law_check_2_3_3
  · exact A3_4_9Law_check_2_4_2
  · exact A3_4_9Law_check_3_0_5
  · exact A3_4_9Law_check_3_1_4
  · exact A3_4_9Law_check_3_2_3
  · exact A3_4_9Law_check_3_3_2
  · exact A3_4_9Law_check_3_4_1
lemma A3_4_9Law_sound (u : Shape) :
    (A3_4_9Law u).Encloses (stageALaw (shape 3 4 9) u : ℝ) := by
  by_cases hu : u ∈ below (shape 3 4 9)
  · have h := contains_sound (Ball.mul_sound (A3_4_9Raw_sound u hu)
      (Ball.inv_sound A3_4_9Den_sound A3_4_9Den_positive)) (A3_4_9Law_check u hu)
    simpa only [A3_4_9Law, hu, ite_true, if_true, stageALaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [A3_4_9Law, hu, ite_false, if_false, stageALaw, splitLaw, Rat.cast_zero]
    simpa only [Rat.cast_zero] using Ball.exact_sound 0

end MatrixMultiplication.NativeNumerics

end
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
lemma AProbsTable_sound_oai (g : Shape) (hg : g ∈ positiveInitial) (u : Shape) :
    (AProbsTable g u).Encloses (stageALaw g u : ℝ) := by
  rw [positiveInitial_list] at hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A1_1_14Law_sound u
  · exact A1_2_13Law_sound u
  · exact A1_3_12Law_sound u
  · exact A1_4_11Law_sound u
  · exact A1_5_10Law_sound u
  · exact A1_6_9Law_sound u
  · exact A1_7_8Law_sound u
  · exact A2_2_12Law_sound u
  · exact A2_3_11Law_sound u
  · exact A2_4_10Law_sound u
  · exact A2_5_9Law_sound u
  · exact A2_6_8Law_sound u
  · exact A2_7_7Law_sound u
  · exact A3_3_10Law_sound u
  · exact A3_4_9Law_sound u
  · exact A3_5_8Law_sound u
  · exact A3_6_7Law_sound u
  · exact A4_4_8Law_sound u
  · exact A4_5_7Law_sound u
  · exact A4_6_6Law_sound u
  · exact A5_5_6Law_sound u

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.AProbsTable_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.AProbsTable_sound_oai
