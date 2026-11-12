-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A1_7_8Raw_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T05:56:12.576748+00:00
-- url     : https://prove2.me/submissions/480afb2c-62e7-4a67-822e-632f49f2d944

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
lemma w38_sound : w38.Encloses (weight (-46871) : ℝ) := by
  exact weight_enclosed_of_trace (-46871) w38Trace w38S0 w38S1 w38S2 w38S3 w38S4 w38S5
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
lemma w135_sound : w135.Encloses (weight (-9643) : ℝ) := by
  exact weight_enclosed_of_trace (-9643) w135Trace w135S0 w135S1 w135S2 w135S3 w135S4 w135S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w138_sound : w138.Encloses (weight (-8576) : ℝ) := by
  exact weight_enclosed_of_trace (-8576) w138Trace w138S0 w138S1 w138S2 w138S3 w138S4 w138S5
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
lemma w80_sound : w80.Encloses (weight (-25058) : ℝ) := by
  exact weight_enclosed_of_trace (-25058) w80Trace w80S0 w80S1 w80S2 w80S3 w80S4 w80S5
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
lemma w5_sound : w5.Encloses (weight (-95643) : ℝ) := by
  exact weight_enclosed_of_trace (-95643) w5Trace w5S0 w5S1 w5S2 w5S3 w5S4 w5S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w19_sound : w19.Encloses (weight (-62269) : ℝ) := by
  exact weight_enclosed_of_trace (-62269) w19Trace w19S0 w19S1 w19S2 w19S3 w19S4 w19S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

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
lemma A1_7_8Raw_sound_oai (u : Shape) (hu : u ∈ below (shape 1 7 8)) :
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

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A1_7_8Raw_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A1_7_8Raw_sound_oai
