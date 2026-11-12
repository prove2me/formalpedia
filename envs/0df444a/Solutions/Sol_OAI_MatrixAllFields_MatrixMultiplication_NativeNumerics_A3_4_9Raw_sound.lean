-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A3_4_9Raw_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T07:14:06.547022+00:00
-- url     : https://prove2.me/submissions/6dc7f1e9-1a77-4489-a98c-35b3d2f414c3

import Mathlib
import Definitions.Def_OAIQ254M003
import Definitions.Def_OAIQ254M005
import Definitions.Def_OAIQ254M006
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
lemma w173_sound : w173.Encloses (weight (-4721) : ℝ) := by
  exact weight_enclosed_of_trace (-4721) w173Trace w173S0 w173S1 w173S2 w173S3 w173S4 w173S5
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
lemma w36_sound : w36.Encloses (weight (-49297) : ℝ) := by
  exact weight_enclosed_of_trace (-49297) w36Trace w36S0 w36S1 w36S2 w36S3 w36S4 w36S5
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
lemma w144_sound : w144.Encloses (weight (-7447) : ℝ) := by
  exact weight_enclosed_of_trace (-7447) w144Trace w144S0 w144S1 w144S2 w144S3 w144S4 w144S5
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
lemma w95_sound : w95.Encloses (weight (-17874) : ℝ) := by
  exact weight_enclosed_of_trace (-17874) w95Trace w95S0 w95S1 w95S2 w95S3 w95S4 w95S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma w97_sound : w97.Encloses (weight (-17336) : ℝ) := by
  exact weight_enclosed_of_trace (-17336) w97Trace w97S0 w97S1 w97S2 w97S3 w97S4 w97S5
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
lemma w3_sound : w3.Encloses (weight (-96770) : ℝ) := by
  exact weight_enclosed_of_trace (-96770) w3Trace w3S0 w3S1 w3S2 w3S3 w3S4 w3S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

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
lemma A3_4_9Raw_sound_oai (u : Shape) (hu : u ∈ below (shape 3 4 9)) :
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

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A3_4_9Raw_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A3_4_9Raw_sound_oai
