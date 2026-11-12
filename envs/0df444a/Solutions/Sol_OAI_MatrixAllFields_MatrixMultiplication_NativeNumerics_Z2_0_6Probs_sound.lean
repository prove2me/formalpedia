-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z2_0_6Probs_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T14:54:46.975553+00:00
-- url     : https://prove2.me/submissions/5e698b7b-f0bf-449d-9ac1-643e4cf35773

import Mathlib
import Definitions.Def_OAIQ254M006
import Definitions.Def_OAIQ254M007
import Definitions.Def_OAIQ254M011
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_mul_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkPolynomial_sound

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
lemma w54_sound : w54.Encloses (weight (-34674) : ℝ) := by
  exact weight_enclosed_of_trace (-34674) w54Trace w54S0 w54S1 w54S2 w54S3 w54S4 w54S5
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
lemma w136_sound : w136.Encloses (weight (-9623) : ℝ) := by
  exact weight_enclosed_of_trace (-9623) w136Trace w136S0 w136S1 w136S2 w136S3 w136S4 w136S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Four2_0_6
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
lemma Z2_0_6Raw_sound_0 (j : Fin 6) :
    (Z2_0_6Raw (0,j)).Encloses (weight (orderedPairInteger (shape 2 0 6) 0 j) : ℝ) := by
  fin_cases j
  · change (Z2_0_6Raw (0,0)).Encloses (weight (orderedPairInteger (shape 2 0 6) 0 0) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 0 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_0_6Raw (0,1)).Encloses (weight (orderedPairInteger (shape 2 0 6) 0 1) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 0 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_0_6Raw (0,2)).Encloses (weight (orderedPairInteger (shape 2 0 6) 0 2) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 0 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_0_6Raw (0,3)).Encloses (weight (orderedPairInteger (shape 2 0 6) 0 3) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 0 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_0_6Raw (0,4)).Encloses (weight (orderedPairInteger (shape 2 0 6) 0 4) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 0 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_0_6Raw (0,5)).Encloses (weight (orderedPairInteger (shape 2 0 6) 0 5) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 0 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z2_0_6Raw_sound_1 (j : Fin 6) :
    (Z2_0_6Raw (1,j)).Encloses (weight (orderedPairInteger (shape 2 0 6) 1 j) : ℝ) := by
  fin_cases j
  · change (Z2_0_6Raw (1,0)).Encloses (weight (orderedPairInteger (shape 2 0 6) 1 0) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 1 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_0_6Raw (1,1)).Encloses (weight (orderedPairInteger (shape 2 0 6) 1 1) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 1 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_0_6Raw (1,2)).Encloses (weight (orderedPairInteger (shape 2 0 6) 1 2) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 1 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_0_6Raw (1,3)).Encloses (weight (orderedPairInteger (shape 2 0 6) 1 3) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 1 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_0_6Raw (1,4)).Encloses (weight (orderedPairInteger (shape 2 0 6) 1 4) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 1 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_0_6Raw (1,5)).Encloses (weight (orderedPairInteger (shape 2 0 6) 1 5) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 1 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z2_0_6Raw_sound_2 (j : Fin 6) :
    (Z2_0_6Raw (2,j)).Encloses (weight (orderedPairInteger (shape 2 0 6) 2 j) : ℝ) := by
  fin_cases j
  · change (Z2_0_6Raw (2,0)).Encloses (weight (orderedPairInteger (shape 2 0 6) 2 0) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 2 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_0_6Raw (2,1)).Encloses (weight (orderedPairInteger (shape 2 0 6) 2 1) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 2 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_0_6Raw (2,2)).Encloses (weight (orderedPairInteger (shape 2 0 6) 2 2) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 2 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_0_6Raw (2,3)).Encloses (weight (orderedPairInteger (shape 2 0 6) 2 3) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 2 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_0_6Raw (2,4)).Encloses (weight (orderedPairInteger (shape 2 0 6) 2 4) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 2 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_0_6Raw (2,5)).Encloses (weight (orderedPairInteger (shape 2 0 6) 2 5) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 2 5 = (-9623) := by decide +kernel
    rw [he]
    exact w136_sound
lemma Z2_0_6Raw_sound_3 (j : Fin 6) :
    (Z2_0_6Raw (3,j)).Encloses (weight (orderedPairInteger (shape 2 0 6) 3 j) : ℝ) := by
  fin_cases j
  · change (Z2_0_6Raw (3,0)).Encloses (weight (orderedPairInteger (shape 2 0 6) 3 0) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 3 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_0_6Raw (3,1)).Encloses (weight (orderedPairInteger (shape 2 0 6) 3 1) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 3 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_0_6Raw (3,2)).Encloses (weight (orderedPairInteger (shape 2 0 6) 3 2) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 3 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_0_6Raw (3,3)).Encloses (weight (orderedPairInteger (shape 2 0 6) 3 3) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 3 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_0_6Raw (3,4)).Encloses (weight (orderedPairInteger (shape 2 0 6) 3 4) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 3 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_0_6Raw (3,5)).Encloses (weight (orderedPairInteger (shape 2 0 6) 3 5) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 3 5 = (-34674) := by decide +kernel
    rw [he]
    exact w54_sound
lemma Z2_0_6Raw_sound_4 (j : Fin 6) :
    (Z2_0_6Raw (4,j)).Encloses (weight (orderedPairInteger (shape 2 0 6) 4 j) : ℝ) := by
  fin_cases j
  · change (Z2_0_6Raw (4,0)).Encloses (weight (orderedPairInteger (shape 2 0 6) 4 0) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 4 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_0_6Raw (4,1)).Encloses (weight (orderedPairInteger (shape 2 0 6) 4 1) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 4 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_0_6Raw (4,2)).Encloses (weight (orderedPairInteger (shape 2 0 6) 4 2) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 4 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_0_6Raw (4,3)).Encloses (weight (orderedPairInteger (shape 2 0 6) 4 3) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 4 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_0_6Raw (4,4)).Encloses (weight (orderedPairInteger (shape 2 0 6) 4 4) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 4 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_0_6Raw (4,5)).Encloses (weight (orderedPairInteger (shape 2 0 6) 4 5) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 4 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z2_0_6Raw_sound_5 (j : Fin 6) :
    (Z2_0_6Raw (5,j)).Encloses (weight (orderedPairInteger (shape 2 0 6) 5 j) : ℝ) := by
  fin_cases j
  · change (Z2_0_6Raw (5,0)).Encloses (weight (orderedPairInteger (shape 2 0 6) 5 0) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 5 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_0_6Raw (5,1)).Encloses (weight (orderedPairInteger (shape 2 0 6) 5 1) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 5 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_0_6Raw (5,2)).Encloses (weight (orderedPairInteger (shape 2 0 6) 5 2) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 5 2 = (-9623) := by decide +kernel
    rw [he]
    exact w136_sound
  · change (Z2_0_6Raw (5,3)).Encloses (weight (orderedPairInteger (shape 2 0 6) 5 3) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 5 3 = (-34674) := by decide +kernel
    rw [he]
    exact w54_sound
  · change (Z2_0_6Raw (5,4)).Encloses (weight (orderedPairInteger (shape 2 0 6) 5 4) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 5 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_0_6Raw (5,5)).Encloses (weight (orderedPairInteger (shape 2 0 6) 5 5) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 5 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z2_0_6Raw_sound (ij : PairSlot) :
    (Z2_0_6Raw ij).Encloses (weight (orderedPairInteger (shape 2 0 6) ij.1 ij.2) : ℝ) := by
  rcases ij with ⟨i,j⟩
  revert i
  exact forall_fin6 (Z2_0_6Raw_sound_0 j) (Z2_0_6Raw_sound_1 j) (Z2_0_6Raw_sound_2 j) (Z2_0_6Raw_sound_3 j) (Z2_0_6Raw_sound_4 j) (Z2_0_6Raw_sound_5 j)
lemma Z2_0_6Den_sound : Z2_0_6Den.Encloses
    (((orderedPairs (shape 2 0 6)).map (fun ij => weight (orderedPairInteger (shape 2 0 6) ij.1 ij.2))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (orderedPairs (shape 2 0 6)) Z2_0_6Raw
    (fun ij => weight (orderedPairInteger (shape 2 0 6) ij.1 ij.2))
    (fun ij _ => Z2_0_6Raw_sound ij)) (by decide +kernel)
lemma Z2_0_6Den_pos : 0 < Z2_0_6Den.lower := by decide +kernel
lemma Z2_0_6Contains : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j = shapeMax (shape 2 0 6) →
    contains (.mul (Z2_0_6Raw (i,j)) (.inv Z2_0_6Den)) (Z2_0_6Probs (i,j)) = true := by
  decide +kernel
lemma Z2_0_6Zero : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j ≠ shapeMax (shape 2 0 6) → Z2_0_6Probs (i,j) = .exact 0 := by
  decide +kernel
lemma Z2_0_6Probs_sound_oai (ij : PairSlot) :
    (Z2_0_6Probs ij).Encloses (zeroPairLaw (shape 2 0 6) ij.1 ij.2 : ℝ) := by
  by_cases h : statisticWeight ij.1 + statisticWeight ij.2 = shapeMax (shape 2 0 6)
  · have hb := contains_sound (Ball.mul_sound (Z2_0_6Raw_sound ij)
      (Ball.inv_sound Z2_0_6Den_sound Z2_0_6Den_pos)) (Z2_0_6Contains ij.1 ij.2 h)
    simpa only [zeroPairLaw, h, ite_true, if_true, Rat.cast_div, Rat.cast_mul,
      Rat.cast_inv, div_eq_mul_inv] using hb
  · rw [Z2_0_6Zero ij.1 ij.2 h]
    simpa only [zeroPairLaw, h, ite_false, if_false] using Ball.exact_sound 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z2_0_6Probs_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z2_0_6Probs_sound_oai
