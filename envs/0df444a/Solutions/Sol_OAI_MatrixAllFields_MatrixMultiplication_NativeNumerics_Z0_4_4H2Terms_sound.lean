-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z0_4_4H2Terms_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T14:54:40.993616+00:00
-- url     : https://prove2.me/submissions/c3d1af18-1d7e-44c1-8cc8-5bf88f29e082

import Mathlib
import Definitions.Def_OAIQ254M006
import Definitions.Def_OAIQ254M007
import Definitions.Def_OAIQ254M011
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_mul_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkLog_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkPolynomial_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_entropyTerm_ball

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

theorem ofBounds_sound {lo hi : ℚ} {x : ℝ}
    (hlo : (lo : ℝ) ≤ x) (hhi : x ≤ (hi : ℝ)) :
    (ofBounds lo hi).Encloses x := by
  simp only [Encloses, ofBounds, Rat.cast_add, Rat.cast_div, Rat.cast_ofNat,
    Rat.cast_sub]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem add_sound {a b : Ball} {x y : ℝ} (hx : a.Encloses x) (hy : b.Encloses y) :
    (add a b).Encloses (x + y) := by
  unfold Encloses add
  simp only [Rat.cast_add]
  calc
    _ = |(x - (a.center : ℝ)) + (y - (b.center : ℝ))| := by congr 1; ring
    _ ≤ |x - (a.center : ℝ)| + |y - (b.center : ℝ)| := abs_add_le _ _
    _ ≤ _ := add_le_add hx hy

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
lemma w205_sound : w205.Encloses (weight (22289) : ℝ) := by
  exact weight_enclosed_of_trace (22289) w205Trace w205S0 w205S1 w205S2 w205S3 w205S4 w205S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w215_sound : w215.Encloses (weight (29263) : ℝ) := by
  exact weight_enclosed_of_trace (29263) w215Trace w215S0 w215S1 w215S2 w215S3 w215S4 w215S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w222_sound : w222.Encloses (weight (45052) : ℝ) := by
  exact weight_enclosed_of_trace (45052) w222Trace w222S0 w222S1 w222S2 w222S3 w222S4 w222S5
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
lemma w121_sound : w121.Encloses (weight (-12831) : ℝ) := by
  exact weight_enclosed_of_trace (-12831) w121Trace w121S0 w121S1 w121S2 w121S3 w121S4 w121S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
lemma Z0_4_4Raw_sound_0 (j : Fin 6) :
    (Z0_4_4Raw (0,j)).Encloses (weight (orderedPairInteger (shape 0 4 4) 0 j) : ℝ) := by
  fin_cases j
  · change (Z0_4_4Raw (0,0)).Encloses (weight (orderedPairInteger (shape 0 4 4) 0 0) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 0 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_4_4Raw (0,1)).Encloses (weight (orderedPairInteger (shape 0 4 4) 0 1) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 0 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_4_4Raw (0,2)).Encloses (weight (orderedPairInteger (shape 0 4 4) 0 2) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 0 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_4_4Raw (0,3)).Encloses (weight (orderedPairInteger (shape 0 4 4) 0 3) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 0 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_4_4Raw (0,4)).Encloses (weight (orderedPairInteger (shape 0 4 4) 0 4) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 0 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_4_4Raw (0,5)).Encloses (weight (orderedPairInteger (shape 0 4 4) 0 5) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 0 5 = (-12831) := by decide +kernel
    rw [he]
    exact w121_sound
lemma Z0_4_4Raw_sound_1 (j : Fin 6) :
    (Z0_4_4Raw (1,j)).Encloses (weight (orderedPairInteger (shape 0 4 4) 1 j) : ℝ) := by
  fin_cases j
  · change (Z0_4_4Raw (1,0)).Encloses (weight (orderedPairInteger (shape 0 4 4) 1 0) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 1 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_4_4Raw (1,1)).Encloses (weight (orderedPairInteger (shape 0 4 4) 1 1) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 1 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_4_4Raw (1,2)).Encloses (weight (orderedPairInteger (shape 0 4 4) 1 2) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 1 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_4_4Raw (1,3)).Encloses (weight (orderedPairInteger (shape 0 4 4) 1 3) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 1 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_4_4Raw (1,4)).Encloses (weight (orderedPairInteger (shape 0 4 4) 1 4) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 1 4 = (29263) := by decide +kernel
    rw [he]
    exact w215_sound
  · change (Z0_4_4Raw (1,5)).Encloses (weight (orderedPairInteger (shape 0 4 4) 1 5) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 1 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_4_4Raw_sound_2 (j : Fin 6) :
    (Z0_4_4Raw (2,j)).Encloses (weight (orderedPairInteger (shape 0 4 4) 2 j) : ℝ) := by
  fin_cases j
  · change (Z0_4_4Raw (2,0)).Encloses (weight (orderedPairInteger (shape 0 4 4) 2 0) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 2 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_4_4Raw (2,1)).Encloses (weight (orderedPairInteger (shape 0 4 4) 2 1) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 2 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_4_4Raw (2,2)).Encloses (weight (orderedPairInteger (shape 0 4 4) 2 2) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 2 2 = (45052) := by decide +kernel
    rw [he]
    exact w222_sound
  · change (Z0_4_4Raw (2,3)).Encloses (weight (orderedPairInteger (shape 0 4 4) 2 3) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 2 3 = (22289) := by decide +kernel
    rw [he]
    exact w205_sound
  · change (Z0_4_4Raw (2,4)).Encloses (weight (orderedPairInteger (shape 0 4 4) 2 4) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 2 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_4_4Raw (2,5)).Encloses (weight (orderedPairInteger (shape 0 4 4) 2 5) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 2 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_4_4Raw_sound_3 (j : Fin 6) :
    (Z0_4_4Raw (3,j)).Encloses (weight (orderedPairInteger (shape 0 4 4) 3 j) : ℝ) := by
  fin_cases j
  · change (Z0_4_4Raw (3,0)).Encloses (weight (orderedPairInteger (shape 0 4 4) 3 0) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 3 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_4_4Raw (3,1)).Encloses (weight (orderedPairInteger (shape 0 4 4) 3 1) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 3 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_4_4Raw (3,2)).Encloses (weight (orderedPairInteger (shape 0 4 4) 3 2) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 3 2 = (22289) := by decide +kernel
    rw [he]
    exact w205_sound
  · change (Z0_4_4Raw (3,3)).Encloses (weight (orderedPairInteger (shape 0 4 4) 3 3) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 3 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_4_4Raw (3,4)).Encloses (weight (orderedPairInteger (shape 0 4 4) 3 4) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 3 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_4_4Raw (3,5)).Encloses (weight (orderedPairInteger (shape 0 4 4) 3 5) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 3 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_4_4Raw_sound_4 (j : Fin 6) :
    (Z0_4_4Raw (4,j)).Encloses (weight (orderedPairInteger (shape 0 4 4) 4 j) : ℝ) := by
  fin_cases j
  · change (Z0_4_4Raw (4,0)).Encloses (weight (orderedPairInteger (shape 0 4 4) 4 0) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 4 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_4_4Raw (4,1)).Encloses (weight (orderedPairInteger (shape 0 4 4) 4 1) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 4 1 = (29263) := by decide +kernel
    rw [he]
    exact w215_sound
  · change (Z0_4_4Raw (4,2)).Encloses (weight (orderedPairInteger (shape 0 4 4) 4 2) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 4 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_4_4Raw (4,3)).Encloses (weight (orderedPairInteger (shape 0 4 4) 4 3) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 4 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_4_4Raw (4,4)).Encloses (weight (orderedPairInteger (shape 0 4 4) 4 4) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 4 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_4_4Raw (4,5)).Encloses (weight (orderedPairInteger (shape 0 4 4) 4 5) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 4 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_4_4Raw_sound_5 (j : Fin 6) :
    (Z0_4_4Raw (5,j)).Encloses (weight (orderedPairInteger (shape 0 4 4) 5 j) : ℝ) := by
  fin_cases j
  · change (Z0_4_4Raw (5,0)).Encloses (weight (orderedPairInteger (shape 0 4 4) 5 0) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 5 0 = (-12831) := by decide +kernel
    rw [he]
    exact w121_sound
  · change (Z0_4_4Raw (5,1)).Encloses (weight (orderedPairInteger (shape 0 4 4) 5 1) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 5 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_4_4Raw (5,2)).Encloses (weight (orderedPairInteger (shape 0 4 4) 5 2) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 5 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_4_4Raw (5,3)).Encloses (weight (orderedPairInteger (shape 0 4 4) 5 3) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 5 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_4_4Raw (5,4)).Encloses (weight (orderedPairInteger (shape 0 4 4) 5 4) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 5 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_4_4Raw (5,5)).Encloses (weight (orderedPairInteger (shape 0 4 4) 5 5) : ℝ)
    have he : orderedPairInteger (shape 0 4 4) 5 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_4_4Raw_sound (ij : PairSlot) :
    (Z0_4_4Raw ij).Encloses (weight (orderedPairInteger (shape 0 4 4) ij.1 ij.2) : ℝ) := by
  rcases ij with ⟨i,j⟩
  revert i
  exact forall_fin6 (Z0_4_4Raw_sound_0 j) (Z0_4_4Raw_sound_1 j) (Z0_4_4Raw_sound_2 j) (Z0_4_4Raw_sound_3 j) (Z0_4_4Raw_sound_4 j) (Z0_4_4Raw_sound_5 j)
lemma Z0_4_4Den_sound : Z0_4_4Den.Encloses
    (((orderedPairs (shape 0 4 4)).map (fun ij => weight (orderedPairInteger (shape 0 4 4) ij.1 ij.2))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (orderedPairs (shape 0 4 4)) Z0_4_4Raw
    (fun ij => weight (orderedPairInteger (shape 0 4 4) ij.1 ij.2))
    (fun ij _ => Z0_4_4Raw_sound ij)) (by decide +kernel)
lemma Z0_4_4Den_pos : 0 < Z0_4_4Den.lower := by decide +kernel
lemma Z0_4_4Contains : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j = shapeMax (shape 0 4 4) →
    contains (.mul (Z0_4_4Raw (i,j)) (.inv Z0_4_4Den)) (Z0_4_4Probs (i,j)) = true := by
  decide +kernel
lemma Z0_4_4Zero : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j ≠ shapeMax (shape 0 4 4) → Z0_4_4Probs (i,j) = .exact 0 := by
  decide +kernel
lemma Z0_4_4Probs_sound (ij : PairSlot) :
    (Z0_4_4Probs ij).Encloses (zeroPairLaw (shape 0 4 4) ij.1 ij.2 : ℝ) := by
  by_cases h : statisticWeight ij.1 + statisticWeight ij.2 = shapeMax (shape 0 4 4)
  · have hb := contains_sound (Ball.mul_sound (Z0_4_4Raw_sound ij)
      (Ball.inv_sound Z0_4_4Den_sound Z0_4_4Den_pos)) (Z0_4_4Contains ij.1 ij.2 h)
    simpa only [zeroPairLaw, h, ite_true, if_true, Rat.cast_div, Rat.cast_mul,
      Rat.cast_inv, div_eq_mul_inv] using hb
  · rw [Z0_4_4Zero ij.1 ij.2 h]
    simpa only [zeroPairLaw, h, ite_false, if_false] using Ball.exact_sound 0

lemma Z0_4_4Half_sound (w : Fin 3) (ij : PairSlot) :
    (Z0_4_4Half w ij).Encloses (halfLaw (shape 0 4 4) w ij : ℝ) := by
  have hp : positive (shape 0 4 4) = false := by decide +kernel
  simp only [Z0_4_4Half, halfLaw, hp, Bool.false_eq_true, ite_false, if_false]
  split_ifs
  · exact Ball.exact_sound 1
  · exact Ball.exact_sound 0
  · exact Z0_4_4Probs_sound _
  · exact Z0_4_4Probs_sound _

lemma Z0_4_4H2E_5_0Log_sound : Z0_4_4H2E_5_0Log.Encloses (Real.log (Z0_4_4H2Value ((5,0) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z0_4_4Half_sound 2) ((5,0) : PairSlot)) (w := Z0_4_4H2E_5_0LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z0_4_4H2E_5_0_sound : Z0_4_4H2E_5_0.Encloses (Foundation.entropyTerm (Z0_4_4H2Value ((5,0) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z0_4_4Half_sound 2) ((5,0) : PairSlot)) Z0_4_4H2E_5_0Log_sound) (by decide +kernel)
lemma Z0_4_4H2E_4_1Log_sound : Z0_4_4H2E_4_1Log.Encloses (Real.log (Z0_4_4H2Value ((4,1) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z0_4_4Half_sound 2) ((4,1) : PairSlot)) (w := Z0_4_4H2E_4_1LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z0_4_4H2E_4_1_sound : Z0_4_4H2E_4_1.Encloses (Foundation.entropyTerm (Z0_4_4H2Value ((4,1) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z0_4_4Half_sound 2) ((4,1) : PairSlot)) Z0_4_4H2E_4_1Log_sound) (by decide +kernel)
lemma Z0_4_4H2E_2_2Log_sound : Z0_4_4H2E_2_2Log.Encloses (Real.log (Z0_4_4H2Value ((2,2) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z0_4_4Half_sound 2) ((2,2) : PairSlot)) (w := Z0_4_4H2E_2_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z0_4_4H2E_2_2_sound : Z0_4_4H2E_2_2.Encloses (Foundation.entropyTerm (Z0_4_4H2Value ((2,2) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z0_4_4Half_sound 2) ((2,2) : PairSlot)) Z0_4_4H2E_2_2Log_sound) (by decide +kernel)
lemma Z0_4_4H2E_2_3Log_sound : Z0_4_4H2E_2_3Log.Encloses (Real.log (Z0_4_4H2Value ((2,3) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z0_4_4Half_sound 2) ((2,3) : PairSlot)) (w := Z0_4_4H2E_2_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z0_4_4H2E_2_3_sound : Z0_4_4H2E_2_3.Encloses (Foundation.entropyTerm (Z0_4_4H2Value ((2,3) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z0_4_4Half_sound 2) ((2,3) : PairSlot)) Z0_4_4H2E_2_3Log_sound) (by decide +kernel)
lemma Z0_4_4H2E_3_2Log_sound : Z0_4_4H2E_3_2Log.Encloses (Real.log (Z0_4_4H2Value ((3,2) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z0_4_4Half_sound 2) ((3,2) : PairSlot)) (w := Z0_4_4H2E_3_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z0_4_4H2E_3_2_sound : Z0_4_4H2E_3_2.Encloses (Foundation.entropyTerm (Z0_4_4H2Value ((3,2) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z0_4_4Half_sound 2) ((3,2) : PairSlot)) Z0_4_4H2E_3_2Log_sound) (by decide +kernel)
lemma Z0_4_4H2E_3_3Log_sound : Z0_4_4H2E_3_3Log.Encloses (Real.log (Z0_4_4H2Value ((3,3) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z0_4_4Half_sound 2) ((3,3) : PairSlot)) (w := Z0_4_4H2E_3_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z0_4_4H2E_3_3_sound : Z0_4_4H2E_3_3.Encloses (Foundation.entropyTerm (Z0_4_4H2Value ((3,3) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z0_4_4Half_sound 2) ((3,3) : PairSlot)) Z0_4_4H2E_3_3Log_sound) (by decide +kernel)
lemma Z0_4_4H2E_1_4Log_sound : Z0_4_4H2E_1_4Log.Encloses (Real.log (Z0_4_4H2Value ((1,4) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z0_4_4Half_sound 2) ((1,4) : PairSlot)) (w := Z0_4_4H2E_1_4LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z0_4_4H2E_1_4_sound : Z0_4_4H2E_1_4.Encloses (Foundation.entropyTerm (Z0_4_4H2Value ((1,4) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z0_4_4Half_sound 2) ((1,4) : PairSlot)) Z0_4_4H2E_1_4Log_sound) (by decide +kernel)
lemma Z0_4_4H2E_0_5Log_sound : Z0_4_4H2E_0_5Log.Encloses (Real.log (Z0_4_4H2Value ((0,5) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z0_4_4Half_sound 2) ((0,5) : PairSlot)) (w := Z0_4_4H2E_0_5LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z0_4_4H2E_0_5_sound : Z0_4_4H2E_0_5.Encloses (Foundation.entropyTerm (Z0_4_4H2Value ((0,5) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z0_4_4Half_sound 2) ((0,5) : PairSlot)) Z0_4_4H2E_0_5Log_sound) (by decide +kernel)
lemma Z0_4_4H2Terms_sound_oai (a : PairSlot) :
    (Z0_4_4H2Terms a).Encloses (Foundation.entropyTerm (Z0_4_4H2Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_4_4Half_sound 2) ((0,0) : PairSlot))) (entropyTerm_zero_ball ((Z0_4_4Half_sound 2) ((0,1) : PairSlot))) (entropyTerm_zero_ball ((Z0_4_4Half_sound 2) ((0,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_4_4Half_sound 2) ((0,3) : PairSlot))) (entropyTerm_zero_ball ((Z0_4_4Half_sound 2) ((0,4) : PairSlot))) Z0_4_4H2E_0_5_sound
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_4_4Half_sound 2) ((1,0) : PairSlot))) (entropyTerm_zero_ball ((Z0_4_4Half_sound 2) ((1,1) : PairSlot))) (entropyTerm_zero_ball ((Z0_4_4Half_sound 2) ((1,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_4_4Half_sound 2) ((1,3) : PairSlot))) Z0_4_4H2E_1_4_sound (entropyTerm_zero_ball ((Z0_4_4Half_sound 2) ((1,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_4_4Half_sound 2) ((2,0) : PairSlot))) (entropyTerm_zero_ball ((Z0_4_4Half_sound 2) ((2,1) : PairSlot))) Z0_4_4H2E_2_2_sound Z0_4_4H2E_2_3_sound (entropyTerm_zero_ball ((Z0_4_4Half_sound 2) ((2,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_4_4Half_sound 2) ((2,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_4_4Half_sound 2) ((3,0) : PairSlot))) (entropyTerm_zero_ball ((Z0_4_4Half_sound 2) ((3,1) : PairSlot))) Z0_4_4H2E_3_2_sound Z0_4_4H2E_3_3_sound (entropyTerm_zero_ball ((Z0_4_4Half_sound 2) ((3,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_4_4Half_sound 2) ((3,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_4_4Half_sound 2) ((4,0) : PairSlot))) Z0_4_4H2E_4_1_sound (entropyTerm_zero_ball ((Z0_4_4Half_sound 2) ((4,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_4_4Half_sound 2) ((4,3) : PairSlot))) (entropyTerm_zero_ball ((Z0_4_4Half_sound 2) ((4,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_4_4Half_sound 2) ((4,5) : PairSlot)))
  · exact forall_fin6 Z0_4_4H2E_5_0_sound (entropyTerm_zero_ball ((Z0_4_4Half_sound 2) ((5,1) : PairSlot))) (entropyTerm_zero_ball ((Z0_4_4Half_sound 2) ((5,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_4_4Half_sound 2) ((5,3) : PairSlot))) (entropyTerm_zero_ball ((Z0_4_4Half_sound 2) ((5,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_4_4Half_sound 2) ((5,5) : PairSlot)))

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z0_4_4H2Terms_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z0_4_4H2Terms_sound_oai
