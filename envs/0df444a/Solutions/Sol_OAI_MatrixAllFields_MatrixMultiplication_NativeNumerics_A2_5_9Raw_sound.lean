-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A2_5_9Raw_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T05:58:18.962726+00:00
-- url     : https://prove2.me/submissions/c48acc2f-68df-49bf-b837-758df2df1d12

import Mathlib
import Definitions.Def_OAIQ254M003
import Definitions.Def_OAIQ254M005
import Definitions.Def_OAIQ254M006
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkPolynomial_sound

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
lemma w181_sound : w181.Encloses (weight (-3578) : ℝ) := by
  exact weight_enclosed_of_trace (-3578) w181Trace w181S0 w181S1 w181S2 w181S3 w181S4 w181S5
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
lemma w39_sound : w39.Encloses (weight (-46655) : ℝ) := by
  exact weight_enclosed_of_trace (-46655) w39Trace w39S0 w39S1 w39S2 w39S3 w39S4 w39S5
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
lemma w137_sound : w137.Encloses (weight (-8700) : ℝ) := by
  exact weight_enclosed_of_trace (-8700) w137Trace w137S0 w137S1 w137S2 w137S3 w137S4 w137S5
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
lemma w82_sound : w82.Encloses (weight (-24599) : ℝ) := by
  exact weight_enclosed_of_trace (-24599) w82Trace w82S0 w82S1 w82S2 w82S3 w82S4 w82S5
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
lemma w6_sound : w6.Encloses (weight (-92989) : ℝ) := by
  exact weight_enclosed_of_trace (-92989) w6Trace w6S0 w6S1 w6S2 w6S3 w6S4 w6S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

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
lemma A2_5_9Raw_sound_oai (u : Shape) (hu : u ∈ below (shape 2 5 9)) :
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

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A2_5_9Raw_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A2_5_9Raw_sound_oai
