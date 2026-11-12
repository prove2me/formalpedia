-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB1_2_5I0_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T07:19:34.727946+00:00
-- url     : https://prove2.me/submissions/5027e68b-00af-418c-8c56-a921e3e8fb51

import Mathlib
import Definitions.Def_OAIQ254M006
import Definitions.Def_OAIQ254M010
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_mul_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkLog_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkPolynomial_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_CompactCertificate_entropyLookup_sound
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

theorem neg_sound {a : Ball} {x : ℝ} (hx : a.Encloses x) :
    (neg a).Encloses (-x) := by
  simpa only [Encloses, neg, Rat.cast_neg, neg_sub_neg, abs_sub_comm] using hx

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
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.shapeValue_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inl
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

lemma finSumBall_sound (n : ℕ) (b : Fin n → Ball) (v : Fin n → ℝ)
    (h : ∀ i, (b i).Encloses (v i)) :
    (finSumBall n b).Encloses (∑ i, v i) := by
  induction n with
  | zero => simpa [finSumBall] using Ball.exact_sound 0
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    exact Ball.add_sound (h 0) (ih _ _ (fun i => h i.succ))

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

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators

lemma entropyFin_enclosed (n : ℕ) (p : Fin n → ℝ) (bs : Fin n → Ball)
    (h : ∀ i, (bs i).Encloses (Foundation.entropyTerm (p i))) :
    (finSumBall n bs).Encloses (Foundation.finiteEntropy p) :=
  finSumBall_sound n _ _ h

lemma homogeneous_enclosed {A : Type*} [Fintype A] (p : A → ℝ)
    {b e : Ball} (hb : b.Encloses (Foundation.entropyTerm (∑ a, p a)))
    (he : e.Encloses (Foundation.finiteEntropy p)) :
    (Ball.add (Ball.neg b) e).Encloses (homogeneousEntropy p) := by
  convert Ball.add_sound (Ball.neg_sound hb) he using 1
  all_goals try with_reducible_and_instances rfl
  simp only [homogeneousEntropy, Foundation.entropyTerm, neg_mul, neg_neg]

lemma marginalBall_sound (support : List Shape) (bs : Shape → Ball) (p : Shape → ℝ)
    (h : ∀ u ∈ support, (bs u).Encloses (p u)) (side : Fin 3) (k : Fin 17) :
    (marginalBall support bs side k).Encloses (marginal support p side k) := by
  apply listSumBall_sound
  intro u hu
  by_cases hk : u side = k.val
  · simpa only [hk, ite_true, if_true] using h u hu
  · simpa only [hk, ite_false, if_false, Rat.cast_zero] using Ball.exact_sound 0

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
lemma w167_sound : w167.Encloses (weight (-5561) : ℝ) := by
  exact weight_enclosed_of_trace (-5561) w167Trace w167S0 w167S1 w167S2 w167S3 w167S4 w167S5
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
lemma w27_sound : w27.Encloses (weight (-55254) : ℝ) := by
  exact weight_enclosed_of_trace (-55254) w27Trace w27S0 w27S1 w27S2 w27S3 w27S4 w27S5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_LittleB1_3_4
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
lemma B1_2_5_below : below (shape 1 2 5) = [
  (shape 0 0 4),
  (shape 0 1 3),
  (shape 0 2 2),
  (shape 1 0 3),
  (shape 1 1 2),
  (shape 1 2 1)] := by decide +kernel
lemma B1_2_5Raw_0_0_4 : (B1_2_5Raw (shape 0 0 4)).Encloses (splitWeight positiveSecond tablep (shape 1 2 5) (shape 0 0 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 1 2 5) (shape 0 0 4)
    (0) (-5561) (-55254) w195 w167 w27
    (by decide +kernel) w195_sound w167_sound w27_sound) (by decide +kernel)
lemma B1_2_5Raw_0_1_3 : (B1_2_5Raw (shape 0 1 3)).Encloses (splitWeight positiveSecond tablep (shape 1 2 5) (shape 0 1 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 1 2 5) (shape 0 1 3)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma B1_2_5Raw_0_2_2 : (B1_2_5Raw (shape 0 2 2)).Encloses (splitWeight positiveSecond tablep (shape 1 2 5) (shape 0 2 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 1 2 5) (shape 0 2 2)
    (0) (-5561) (0) w195 w167 w195
    (by decide +kernel) w195_sound w167_sound w195_sound) (by decide +kernel)
lemma B1_2_5Raw_1_0_3 : (B1_2_5Raw (shape 1 0 3)).Encloses (splitWeight positiveSecond tablep (shape 1 2 5) (shape 1 0 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 1 2 5) (shape 1 0 3)
    (0) (-5561) (0) w195 w167 w195
    (by decide +kernel) w195_sound w167_sound w195_sound) (by decide +kernel)
lemma B1_2_5Raw_1_1_2 : (B1_2_5Raw (shape 1 1 2)).Encloses (splitWeight positiveSecond tablep (shape 1 2 5) (shape 1 1 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 1 2 5) (shape 1 1 2)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma B1_2_5Raw_1_2_1 : (B1_2_5Raw (shape 1 2 1)).Encloses (splitWeight positiveSecond tablep (shape 1 2 5) (shape 1 2 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 1 2 5) (shape 1 2 1)
    (0) (-5561) (-55254) w195 w167 w27
    (by decide +kernel) w195_sound w167_sound w27_sound) (by decide +kernel)
lemma B1_2_5Raw_sound (u : Shape) (hu : u ∈ below (shape 1 2 5)) :
    (B1_2_5Raw u).Encloses (splitWeight positiveSecond tablep (shape 1 2 5) u : ℝ) := by
  rw [B1_2_5_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · exact B1_2_5Raw_0_0_4
  · exact B1_2_5Raw_0_1_3
  · exact B1_2_5Raw_0_2_2
  · exact B1_2_5Raw_1_0_3
  · exact B1_2_5Raw_1_1_2
  · exact B1_2_5Raw_1_2_1
lemma B1_2_5Den_sound : B1_2_5Den.Encloses (((below (shape 1 2 5)).map (splitWeight positiveSecond tablep (shape 1 2 5))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (below (shape 1 2 5)) B1_2_5Raw (splitWeight positiveSecond tablep (shape 1 2 5)) B1_2_5Raw_sound) (by decide +kernel)
lemma B1_2_5Den_positive : 0 < B1_2_5Den.lower := by decide +kernel
lemma B1_2_5Law_check_0_0_4 : contains (.mul (B1_2_5Raw (shape 0 0 4)) (.inv B1_2_5Den)) (B1_2_5Table (shape 0 0 4)) = true := by decide +kernel
lemma B1_2_5Law_check_0_1_3 : contains (.mul (B1_2_5Raw (shape 0 1 3)) (.inv B1_2_5Den)) (B1_2_5Table (shape 0 1 3)) = true := by decide +kernel
lemma B1_2_5Law_check_0_2_2 : contains (.mul (B1_2_5Raw (shape 0 2 2)) (.inv B1_2_5Den)) (B1_2_5Table (shape 0 2 2)) = true := by decide +kernel
lemma B1_2_5Law_check_1_0_3 : contains (.mul (B1_2_5Raw (shape 1 0 3)) (.inv B1_2_5Den)) (B1_2_5Table (shape 1 0 3)) = true := by decide +kernel
lemma B1_2_5Law_check_1_1_2 : contains (.mul (B1_2_5Raw (shape 1 1 2)) (.inv B1_2_5Den)) (B1_2_5Table (shape 1 1 2)) = true := by decide +kernel
lemma B1_2_5Law_check_1_2_1 : contains (.mul (B1_2_5Raw (shape 1 2 1)) (.inv B1_2_5Den)) (B1_2_5Table (shape 1 2 1)) = true := by decide +kernel
lemma B1_2_5Law_check (u : Shape) (hu : u ∈ below (shape 1 2 5)) :
    contains (.mul (B1_2_5Raw u) (.inv B1_2_5Den)) (B1_2_5Table u) = true := by
  rw [B1_2_5_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · exact B1_2_5Law_check_0_0_4
  · exact B1_2_5Law_check_0_1_3
  · exact B1_2_5Law_check_0_2_2
  · exact B1_2_5Law_check_1_0_3
  · exact B1_2_5Law_check_1_1_2
  · exact B1_2_5Law_check_1_2_1
lemma B1_2_5Law_sound (u : Shape) :
    (B1_2_5Law u).Encloses (stageBLaw (shape 1 2 5) u : ℝ) := by
  by_cases hu : u ∈ below (shape 1 2 5)
  · have h := contains_sound (Ball.mul_sound (B1_2_5Raw_sound u hu)
      (Ball.inv_sound B1_2_5Den_sound B1_2_5Den_positive)) (B1_2_5Law_check u hu)
    simpa only [B1_2_5Law, hu, ite_true, if_true, stageBLaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [B1_2_5Law, hu, ite_false, if_false, stageBLaw, splitLaw, Rat.cast_zero]
    simpa only [Rat.cast_zero] using Ball.exact_sound 0

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB1_2_5I0
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
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
lemma CB1_2_5I0Raw_sound (a : Fin 17) :
    (CB1_2_5I0Raw a).Encloses (CB1_2_5I0Value a) := by
  exact marginalBall_sound (below (shape 1 2 5)) B1_2_5Law (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (fun u _ => B1_2_5Law_sound u) ((stageBPriority (shape 1 2 5)) 0) a
lemma CB1_2_5I0Certificates_valid :
    CB1_2_5I0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB1_2_5I0P_check : ∀ a : Fin 17, contains (CB1_2_5I0Raw a) (CB1_2_5I0P a) = true := by
  decide +kernel
lemma CB1_2_5I0P_sound (a : Fin 17) :
    (CB1_2_5I0P a).Encloses (CB1_2_5I0Value a) :=
  contains_sound (CB1_2_5I0Raw_sound a) (CB1_2_5I0P_check a)
lemma CB1_2_5I0Terms_sound (a : Fin 17) :
    (CB1_2_5I0Terms a).Encloses (Foundation.entropyTerm (CB1_2_5I0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_2_5I0Certificates_valid
    (CB1_2_5I0CertificateIndex a) (CB1_2_5I0P_sound a)
lemma CB1_2_5I0Entropy_sound : CB1_2_5I0Entropy.Encloses (Foundation.finiteEntropy CB1_2_5I0Value) := by
  exact contains_sound (entropyFin_enclosed 17 CB1_2_5I0Value CB1_2_5I0Terms CB1_2_5I0Terms_sound) (by decide +kernel)
lemma CB1_2_5I0Mass_sound : CB1_2_5I0Mass.Encloses (∑ a, CB1_2_5I0Value a) := by
  exact contains_sound (finSumBall_sound 17 CB1_2_5I0P CB1_2_5I0Value CB1_2_5I0P_sound) (by decide +kernel)
lemma CB1_2_5I0MassTermLog_sound : CB1_2_5I0MassTermLog.Encloses (Real.log ((∑ a, CB1_2_5I0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB1_2_5I0Mass_sound) (w := CB1_2_5I0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CB1_2_5I0MassTerm_sound : CB1_2_5I0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_2_5I0Value a))) := by
  exact contains_sound (entropyTerm_ball (CB1_2_5I0Mass_sound) CB1_2_5I0MassTermLog_sound) (by decide +kernel)
lemma CB1_2_5I0H_sound : CB1_2_5I0H.Encloses (homogeneousEntropy CB1_2_5I0Value) := by
  exact contains_sound (homogeneous_enclosed CB1_2_5I0Value CB1_2_5I0MassTerm_sound CB1_2_5I0Entropy_sound) (by decide +kernel)
lemma CB1_2_5I0_sound_oai : CB1_2_5I0H.Encloses (stageBCapacity (shape 1 2 5) 0) := by
  exact CB1_2_5I0H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB1_2_5I0_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB1_2_5I0_sound_oai
