-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_2_13I2ResidualEntropies_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:38:56.051986+00:00
-- url     : https://prove2.me/submissions/581ad1d1-0085-41d4-94e6-64ae07a9cae0

import Mathlib
import Definitions.Def_OAIQ254M006
import Definitions.Def_OAIQ254M007
import Definitions.Def_OAIQ254M011
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_mul_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkLog_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkPolynomial_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_CompactCertificate_entropyLookup_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_entropyTerm_ball
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_halfTable_sound

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
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
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

lemma product_fin6_enclosed (bs : Fin 6 → Fin 6 → Ball) (v : PairSlot → ℝ)
    (h : ∀ i j, (bs i j).Encloses (v (i,j))) :
    (finSumBall 6 (fun i => finSumBall 6 (bs i))).Encloses (∑ s : PairSlot, v s) := by
  rw [Fintype.sum_prod_type]
  exact finSumBall_sound 6 _ _ (fun i => finSumBall_sound 6 _ _ (h i))

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

lemma pairSumBall_sound (bs : PairSlot → Ball) (v : PairSlot → ℝ)
    (h : ∀ a, (bs a).Encloses (v a)) :
    (pairSumBall bs).Encloses (∑ a, v a) := by
  exact product_fin6_enclosed _ _ (fun i j => h (i,j))

lemma entropyPair_enclosed (p : PairSlot → ℝ) (bs : PairSlot → Ball)
    (h : ∀ i, (bs i).Encloses (Foundation.entropyTerm (p i))) :
    (pairSumBall bs).Encloses (Foundation.finiteEntropy p) :=
  pairSumBall_sound _ _ h

lemma homogeneous_enclosed {A : Type*} [Fintype A] (p : A → ℝ)
    {b e : Ball} (hb : b.Encloses (Foundation.entropyTerm (∑ a, p a)))
    (he : e.Encloses (Foundation.finiteEntropy p)) :
    (Ball.add (Ball.neg b) e).Encloses (homogeneousEntropy p) := by
  convert Ball.add_sound (Ball.neg_sound hb) he using 1
  all_goals try with_reducible_and_instances rfl
  simp only [homogeneousEntropy, Foundation.entropyTerm, neg_mul, neg_neg]

lemma residualBall_sound_on {A : Type*} [Fintype A] (support : List Shape)
    (bs : Shape → Ball) (p : Shape → ℝ) (priority : Placement) (position : Fin 3)
    (bq : Shape → A → Ball) (q : Shape → A → ℝ)
    (hp : ∀ u ∈ support, (bs u).Encloses (p u))
    (hq : ∀ u ∈ support, ∀ a, (bq u a).Encloses (q u a)) (k : Fin 17) (a : A) :
    (residualBall support bs priority position bq k a).Encloses
      (residualLaw support p priority position q k a) := by
  apply listSumBall_sound
  intro u hu
  by_cases hk : ¬ designated priority position u ∧ u (priority position) = k.val
  · simpa only [ite_eq_left hk] using Ball.mul_sound (hp u hu) (hq u hu a)
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

lemma w198_sound : w198.Encloses (weight (295) : ℝ) := by
  exact weight_enclosed_of_trace (295) w198Trace w198S0 w198S1 w198S2 w198S3 w198S4 w198S5
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
lemma w84_sound : w84.Encloses (weight (-20546) : ℝ) := by
  exact weight_enclosed_of_trace (-20546) w84Trace w84S0 w84S1 w84S2 w84S3 w84S4 w84S5
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
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_2_13I2
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
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
lemma CA1_2_13I2R0Raw_sound (a : PairSlot) :
    (CA1_2_13I2R0Raw a).Encloses (CA1_2_13I2R0Value a) := by
  exact residualBall_sound_on (below (shape 1 2 13)) A1_2_13Law (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_2_13Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 2 13) (show (shape 1 2 13) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 0 a
lemma CA1_2_13I2R0Certificates_valid :
    CA1_2_13I2R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA1_2_13I2R0P_check : ∀ a : PairSlot, contains (CA1_2_13I2R0Raw a) (CA1_2_13I2R0P a) = true := by
  decide +kernel
lemma CA1_2_13I2R0P_sound (a : PairSlot) :
    (CA1_2_13I2R0P a).Encloses (CA1_2_13I2R0Value a) :=
  contains_sound (CA1_2_13I2R0Raw_sound a) (CA1_2_13I2R0P_check a)
lemma CA1_2_13I2R0Terms_sound (a : PairSlot) :
    (CA1_2_13I2R0Terms a).Encloses (Foundation.entropyTerm (CA1_2_13I2R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_2_13I2R0Certificates_valid
    (CA1_2_13I2R0CertificateIndex a) (CA1_2_13I2R0P_sound a)
lemma CA1_2_13I2R0Entropy_sound : CA1_2_13I2R0Entropy.Encloses (Foundation.finiteEntropy CA1_2_13I2R0Value) := by
  exact contains_sound (entropyPair_enclosed CA1_2_13I2R0Value CA1_2_13I2R0Terms CA1_2_13I2R0Terms_sound) (by decide +kernel)
lemma CA1_2_13I2R0Mass_sound : CA1_2_13I2R0Mass.Encloses (∑ a, CA1_2_13I2R0Value a) := by
  exact contains_sound (pairSumBall_sound CA1_2_13I2R0P CA1_2_13I2R0Value CA1_2_13I2R0P_sound) (by decide +kernel)
lemma CA1_2_13I2R0MassTerm_sound : CA1_2_13I2R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_2_13I2R0Value a))) :=
  entropyTerm_zero_ball (CA1_2_13I2R0Mass_sound)
lemma CA1_2_13I2R0H_sound : CA1_2_13I2R0H.Encloses (homogeneousEntropy CA1_2_13I2R0Value) := by
  exact contains_sound (homogeneous_enclosed CA1_2_13I2R0Value CA1_2_13I2R0MassTerm_sound CA1_2_13I2R0Entropy_sound) (by decide +kernel)
lemma CA1_2_13I2R1Raw_sound (a : PairSlot) :
    (CA1_2_13I2R1Raw a).Encloses (CA1_2_13I2R1Value a) := by
  exact residualBall_sound_on (below (shape 1 2 13)) A1_2_13Law (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_2_13Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 2 13) (show (shape 1 2 13) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 1 a
lemma CA1_2_13I2R1Certificates_valid :
    CA1_2_13I2R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA1_2_13I2R1P_check : ∀ a : PairSlot, contains (CA1_2_13I2R1Raw a) (CA1_2_13I2R1P a) = true := by
  decide +kernel
lemma CA1_2_13I2R1P_sound (a : PairSlot) :
    (CA1_2_13I2R1P a).Encloses (CA1_2_13I2R1Value a) :=
  contains_sound (CA1_2_13I2R1Raw_sound a) (CA1_2_13I2R1P_check a)
lemma CA1_2_13I2R1Terms_sound (a : PairSlot) :
    (CA1_2_13I2R1Terms a).Encloses (Foundation.entropyTerm (CA1_2_13I2R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_2_13I2R1Certificates_valid
    (CA1_2_13I2R1CertificateIndex a) (CA1_2_13I2R1P_sound a)
lemma CA1_2_13I2R1Entropy_sound : CA1_2_13I2R1Entropy.Encloses (Foundation.finiteEntropy CA1_2_13I2R1Value) := by
  exact contains_sound (entropyPair_enclosed CA1_2_13I2R1Value CA1_2_13I2R1Terms CA1_2_13I2R1Terms_sound) (by decide +kernel)
lemma CA1_2_13I2R1Mass_sound : CA1_2_13I2R1Mass.Encloses (∑ a, CA1_2_13I2R1Value a) := by
  exact contains_sound (pairSumBall_sound CA1_2_13I2R1P CA1_2_13I2R1Value CA1_2_13I2R1P_sound) (by decide +kernel)
lemma CA1_2_13I2R1MassTerm_sound : CA1_2_13I2R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_2_13I2R1Value a))) :=
  entropyTerm_zero_ball (CA1_2_13I2R1Mass_sound)
lemma CA1_2_13I2R1H_sound : CA1_2_13I2R1H.Encloses (homogeneousEntropy CA1_2_13I2R1Value) := by
  exact contains_sound (homogeneous_enclosed CA1_2_13I2R1Value CA1_2_13I2R1MassTerm_sound CA1_2_13I2R1Entropy_sound) (by decide +kernel)
lemma CA1_2_13I2R2Raw_sound (a : PairSlot) :
    (CA1_2_13I2R2Raw a).Encloses (CA1_2_13I2R2Value a) := by
  exact residualBall_sound_on (below (shape 1 2 13)) A1_2_13Law (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_2_13Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 2 13) (show (shape 1 2 13) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 2 a
lemma CA1_2_13I2R2Certificates_valid :
    CA1_2_13I2R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA1_2_13I2R2P_check : ∀ a : PairSlot, contains (CA1_2_13I2R2Raw a) (CA1_2_13I2R2P a) = true := by
  decide +kernel
lemma CA1_2_13I2R2P_sound (a : PairSlot) :
    (CA1_2_13I2R2P a).Encloses (CA1_2_13I2R2Value a) :=
  contains_sound (CA1_2_13I2R2Raw_sound a) (CA1_2_13I2R2P_check a)
lemma CA1_2_13I2R2Terms_sound (a : PairSlot) :
    (CA1_2_13I2R2Terms a).Encloses (Foundation.entropyTerm (CA1_2_13I2R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_2_13I2R2Certificates_valid
    (CA1_2_13I2R2CertificateIndex a) (CA1_2_13I2R2P_sound a)
lemma CA1_2_13I2R2Entropy_sound : CA1_2_13I2R2Entropy.Encloses (Foundation.finiteEntropy CA1_2_13I2R2Value) := by
  exact contains_sound (entropyPair_enclosed CA1_2_13I2R2Value CA1_2_13I2R2Terms CA1_2_13I2R2Terms_sound) (by decide +kernel)
lemma CA1_2_13I2R2Mass_sound : CA1_2_13I2R2Mass.Encloses (∑ a, CA1_2_13I2R2Value a) := by
  exact contains_sound (pairSumBall_sound CA1_2_13I2R2P CA1_2_13I2R2Value CA1_2_13I2R2P_sound) (by decide +kernel)
lemma CA1_2_13I2R2MassTerm_sound : CA1_2_13I2R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_2_13I2R2Value a))) :=
  entropyTerm_zero_ball (CA1_2_13I2R2Mass_sound)
lemma CA1_2_13I2R2H_sound : CA1_2_13I2R2H.Encloses (homogeneousEntropy CA1_2_13I2R2Value) := by
  exact contains_sound (homogeneous_enclosed CA1_2_13I2R2Value CA1_2_13I2R2MassTerm_sound CA1_2_13I2R2Entropy_sound) (by decide +kernel)
lemma CA1_2_13I2R3Raw_sound (a : PairSlot) :
    (CA1_2_13I2R3Raw a).Encloses (CA1_2_13I2R3Value a) := by
  exact residualBall_sound_on (below (shape 1 2 13)) A1_2_13Law (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_2_13Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 2 13) (show (shape 1 2 13) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 3 a
lemma CA1_2_13I2R3Certificates_valid :
    CA1_2_13I2R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA1_2_13I2R3P_check : ∀ a : PairSlot, contains (CA1_2_13I2R3Raw a) (CA1_2_13I2R3P a) = true := by
  decide +kernel
lemma CA1_2_13I2R3P_sound (a : PairSlot) :
    (CA1_2_13I2R3P a).Encloses (CA1_2_13I2R3Value a) :=
  contains_sound (CA1_2_13I2R3Raw_sound a) (CA1_2_13I2R3P_check a)
lemma CA1_2_13I2R3Terms_sound (a : PairSlot) :
    (CA1_2_13I2R3Terms a).Encloses (Foundation.entropyTerm (CA1_2_13I2R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_2_13I2R3Certificates_valid
    (CA1_2_13I2R3CertificateIndex a) (CA1_2_13I2R3P_sound a)
lemma CA1_2_13I2R3Entropy_sound : CA1_2_13I2R3Entropy.Encloses (Foundation.finiteEntropy CA1_2_13I2R3Value) := by
  exact contains_sound (entropyPair_enclosed CA1_2_13I2R3Value CA1_2_13I2R3Terms CA1_2_13I2R3Terms_sound) (by decide +kernel)
lemma CA1_2_13I2R3Mass_sound : CA1_2_13I2R3Mass.Encloses (∑ a, CA1_2_13I2R3Value a) := by
  exact contains_sound (pairSumBall_sound CA1_2_13I2R3P CA1_2_13I2R3Value CA1_2_13I2R3P_sound) (by decide +kernel)
lemma CA1_2_13I2R3MassTerm_sound : CA1_2_13I2R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_2_13I2R3Value a))) :=
  entropyTerm_zero_ball (CA1_2_13I2R3Mass_sound)
lemma CA1_2_13I2R3H_sound : CA1_2_13I2R3H.Encloses (homogeneousEntropy CA1_2_13I2R3Value) := by
  exact contains_sound (homogeneous_enclosed CA1_2_13I2R3Value CA1_2_13I2R3MassTerm_sound CA1_2_13I2R3Entropy_sound) (by decide +kernel)
lemma CA1_2_13I2R4Raw_sound (a : PairSlot) :
    (CA1_2_13I2R4Raw a).Encloses (CA1_2_13I2R4Value a) := by
  exact residualBall_sound_on (below (shape 1 2 13)) A1_2_13Law (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_2_13Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 2 13) (show (shape 1 2 13) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 4 a
lemma CA1_2_13I2R4Certificates_valid :
    CA1_2_13I2R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA1_2_13I2R4P_check : ∀ a : PairSlot, contains (CA1_2_13I2R4Raw a) (CA1_2_13I2R4P a) = true := by
  decide +kernel
lemma CA1_2_13I2R4P_sound (a : PairSlot) :
    (CA1_2_13I2R4P a).Encloses (CA1_2_13I2R4Value a) :=
  contains_sound (CA1_2_13I2R4Raw_sound a) (CA1_2_13I2R4P_check a)
lemma CA1_2_13I2R4Terms_sound (a : PairSlot) :
    (CA1_2_13I2R4Terms a).Encloses (Foundation.entropyTerm (CA1_2_13I2R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_2_13I2R4Certificates_valid
    (CA1_2_13I2R4CertificateIndex a) (CA1_2_13I2R4P_sound a)
lemma CA1_2_13I2R4Entropy_sound : CA1_2_13I2R4Entropy.Encloses (Foundation.finiteEntropy CA1_2_13I2R4Value) := by
  exact contains_sound (entropyPair_enclosed CA1_2_13I2R4Value CA1_2_13I2R4Terms CA1_2_13I2R4Terms_sound) (by decide +kernel)
lemma CA1_2_13I2R4Mass_sound : CA1_2_13I2R4Mass.Encloses (∑ a, CA1_2_13I2R4Value a) := by
  exact contains_sound (pairSumBall_sound CA1_2_13I2R4P CA1_2_13I2R4Value CA1_2_13I2R4P_sound) (by decide +kernel)
lemma CA1_2_13I2R4MassTerm_sound : CA1_2_13I2R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_2_13I2R4Value a))) :=
  entropyTerm_zero_ball (CA1_2_13I2R4Mass_sound)
lemma CA1_2_13I2R4H_sound : CA1_2_13I2R4H.Encloses (homogeneousEntropy CA1_2_13I2R4Value) := by
  exact contains_sound (homogeneous_enclosed CA1_2_13I2R4Value CA1_2_13I2R4MassTerm_sound CA1_2_13I2R4Entropy_sound) (by decide +kernel)
lemma CA1_2_13I2R5Raw_sound (a : PairSlot) :
    (CA1_2_13I2R5Raw a).Encloses (CA1_2_13I2R5Value a) := by
  exact residualBall_sound_on (below (shape 1 2 13)) A1_2_13Law (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_2_13Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 2 13) (show (shape 1 2 13) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 5 a
lemma CA1_2_13I2R5Certificates_valid :
    CA1_2_13I2R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA1_2_13I2R5P_check : ∀ a : PairSlot, contains (CA1_2_13I2R5Raw a) (CA1_2_13I2R5P a) = true := by
  decide +kernel
lemma CA1_2_13I2R5P_sound (a : PairSlot) :
    (CA1_2_13I2R5P a).Encloses (CA1_2_13I2R5Value a) :=
  contains_sound (CA1_2_13I2R5Raw_sound a) (CA1_2_13I2R5P_check a)
lemma CA1_2_13I2R5Terms_sound (a : PairSlot) :
    (CA1_2_13I2R5Terms a).Encloses (Foundation.entropyTerm (CA1_2_13I2R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_2_13I2R5Certificates_valid
    (CA1_2_13I2R5CertificateIndex a) (CA1_2_13I2R5P_sound a)
lemma CA1_2_13I2R5Entropy_sound : CA1_2_13I2R5Entropy.Encloses (Foundation.finiteEntropy CA1_2_13I2R5Value) := by
  exact contains_sound (entropyPair_enclosed CA1_2_13I2R5Value CA1_2_13I2R5Terms CA1_2_13I2R5Terms_sound) (by decide +kernel)
lemma CA1_2_13I2R5Mass_sound : CA1_2_13I2R5Mass.Encloses (∑ a, CA1_2_13I2R5Value a) := by
  exact contains_sound (pairSumBall_sound CA1_2_13I2R5P CA1_2_13I2R5Value CA1_2_13I2R5P_sound) (by decide +kernel)
lemma CA1_2_13I2R5MassTermLog_sound : CA1_2_13I2R5MassTermLog.Encloses (Real.log ((∑ a, CA1_2_13I2R5Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_2_13I2R5Mass_sound) (w := CA1_2_13I2R5MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CA1_2_13I2R5MassTerm_sound : CA1_2_13I2R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_2_13I2R5Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_2_13I2R5Mass_sound) CA1_2_13I2R5MassTermLog_sound) (by decide +kernel)
lemma CA1_2_13I2R5H_sound : CA1_2_13I2R5H.Encloses (homogeneousEntropy CA1_2_13I2R5Value) := by
  exact contains_sound (homogeneous_enclosed CA1_2_13I2R5Value CA1_2_13I2R5MassTerm_sound CA1_2_13I2R5Entropy_sound) (by decide +kernel)
lemma CA1_2_13I2R6Raw_sound (a : PairSlot) :
    (CA1_2_13I2R6Raw a).Encloses (CA1_2_13I2R6Value a) := by
  exact residualBall_sound_on (below (shape 1 2 13)) A1_2_13Law (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_2_13Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 2 13) (show (shape 1 2 13) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 6 a
lemma CA1_2_13I2R6Certificates_valid :
    CA1_2_13I2R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA1_2_13I2R6P_check : ∀ a : PairSlot, contains (CA1_2_13I2R6Raw a) (CA1_2_13I2R6P a) = true := by
  decide +kernel
lemma CA1_2_13I2R6P_sound (a : PairSlot) :
    (CA1_2_13I2R6P a).Encloses (CA1_2_13I2R6Value a) :=
  contains_sound (CA1_2_13I2R6Raw_sound a) (CA1_2_13I2R6P_check a)
lemma CA1_2_13I2R6Terms_sound (a : PairSlot) :
    (CA1_2_13I2R6Terms a).Encloses (Foundation.entropyTerm (CA1_2_13I2R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_2_13I2R6Certificates_valid
    (CA1_2_13I2R6CertificateIndex a) (CA1_2_13I2R6P_sound a)
lemma CA1_2_13I2R6Entropy_sound : CA1_2_13I2R6Entropy.Encloses (Foundation.finiteEntropy CA1_2_13I2R6Value) := by
  exact contains_sound (entropyPair_enclosed CA1_2_13I2R6Value CA1_2_13I2R6Terms CA1_2_13I2R6Terms_sound) (by decide +kernel)
lemma CA1_2_13I2R6Mass_sound : CA1_2_13I2R6Mass.Encloses (∑ a, CA1_2_13I2R6Value a) := by
  exact contains_sound (pairSumBall_sound CA1_2_13I2R6P CA1_2_13I2R6Value CA1_2_13I2R6P_sound) (by decide +kernel)
lemma CA1_2_13I2R6MassTermLog_sound : CA1_2_13I2R6MassTermLog.Encloses (Real.log ((∑ a, CA1_2_13I2R6Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_2_13I2R6Mass_sound) (w := CA1_2_13I2R6MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CA1_2_13I2R6MassTerm_sound : CA1_2_13I2R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_2_13I2R6Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_2_13I2R6Mass_sound) CA1_2_13I2R6MassTermLog_sound) (by decide +kernel)
lemma CA1_2_13I2R6H_sound : CA1_2_13I2R6H.Encloses (homogeneousEntropy CA1_2_13I2R6Value) := by
  exact contains_sound (homogeneous_enclosed CA1_2_13I2R6Value CA1_2_13I2R6MassTerm_sound CA1_2_13I2R6Entropy_sound) (by decide +kernel)
lemma CA1_2_13I2R7Raw_sound (a : PairSlot) :
    (CA1_2_13I2R7Raw a).Encloses (CA1_2_13I2R7Value a) := by
  exact residualBall_sound_on (below (shape 1 2 13)) A1_2_13Law (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_2_13Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 2 13) (show (shape 1 2 13) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 7 a
lemma CA1_2_13I2R7Certificates_valid :
    CA1_2_13I2R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA1_2_13I2R7P_check : ∀ a : PairSlot, contains (CA1_2_13I2R7Raw a) (CA1_2_13I2R7P a) = true := by
  decide +kernel
lemma CA1_2_13I2R7P_sound (a : PairSlot) :
    (CA1_2_13I2R7P a).Encloses (CA1_2_13I2R7Value a) :=
  contains_sound (CA1_2_13I2R7Raw_sound a) (CA1_2_13I2R7P_check a)
lemma CA1_2_13I2R7Terms_sound (a : PairSlot) :
    (CA1_2_13I2R7Terms a).Encloses (Foundation.entropyTerm (CA1_2_13I2R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_2_13I2R7Certificates_valid
    (CA1_2_13I2R7CertificateIndex a) (CA1_2_13I2R7P_sound a)
lemma CA1_2_13I2R7Entropy_sound : CA1_2_13I2R7Entropy.Encloses (Foundation.finiteEntropy CA1_2_13I2R7Value) := by
  exact contains_sound (entropyPair_enclosed CA1_2_13I2R7Value CA1_2_13I2R7Terms CA1_2_13I2R7Terms_sound) (by decide +kernel)
lemma CA1_2_13I2R7Mass_sound : CA1_2_13I2R7Mass.Encloses (∑ a, CA1_2_13I2R7Value a) := by
  exact contains_sound (pairSumBall_sound CA1_2_13I2R7P CA1_2_13I2R7Value CA1_2_13I2R7P_sound) (by decide +kernel)
lemma CA1_2_13I2R7MassTerm_sound : CA1_2_13I2R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_2_13I2R7Value a))) :=
  entropyTerm_zero_ball (CA1_2_13I2R7Mass_sound)
lemma CA1_2_13I2R7H_sound : CA1_2_13I2R7H.Encloses (homogeneousEntropy CA1_2_13I2R7Value) := by
  exact contains_sound (homogeneous_enclosed CA1_2_13I2R7Value CA1_2_13I2R7MassTerm_sound CA1_2_13I2R7Entropy_sound) (by decide +kernel)
lemma CA1_2_13I2R8Raw_sound (a : PairSlot) :
    (CA1_2_13I2R8Raw a).Encloses (CA1_2_13I2R8Value a) := by
  exact residualBall_sound_on (below (shape 1 2 13)) A1_2_13Law (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_2_13Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 2 13) (show (shape 1 2 13) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 8 a
lemma CA1_2_13I2R8Certificates_valid :
    CA1_2_13I2R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA1_2_13I2R8P_check : ∀ a : PairSlot, contains (CA1_2_13I2R8Raw a) (CA1_2_13I2R8P a) = true := by
  decide +kernel
lemma CA1_2_13I2R8P_sound (a : PairSlot) :
    (CA1_2_13I2R8P a).Encloses (CA1_2_13I2R8Value a) :=
  contains_sound (CA1_2_13I2R8Raw_sound a) (CA1_2_13I2R8P_check a)
lemma CA1_2_13I2R8Terms_sound (a : PairSlot) :
    (CA1_2_13I2R8Terms a).Encloses (Foundation.entropyTerm (CA1_2_13I2R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_2_13I2R8Certificates_valid
    (CA1_2_13I2R8CertificateIndex a) (CA1_2_13I2R8P_sound a)
lemma CA1_2_13I2R8Entropy_sound : CA1_2_13I2R8Entropy.Encloses (Foundation.finiteEntropy CA1_2_13I2R8Value) := by
  exact contains_sound (entropyPair_enclosed CA1_2_13I2R8Value CA1_2_13I2R8Terms CA1_2_13I2R8Terms_sound) (by decide +kernel)
lemma CA1_2_13I2R8Mass_sound : CA1_2_13I2R8Mass.Encloses (∑ a, CA1_2_13I2R8Value a) := by
  exact contains_sound (pairSumBall_sound CA1_2_13I2R8P CA1_2_13I2R8Value CA1_2_13I2R8P_sound) (by decide +kernel)
lemma CA1_2_13I2R8MassTerm_sound : CA1_2_13I2R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_2_13I2R8Value a))) :=
  entropyTerm_zero_ball (CA1_2_13I2R8Mass_sound)
lemma CA1_2_13I2R8H_sound : CA1_2_13I2R8H.Encloses (homogeneousEntropy CA1_2_13I2R8Value) := by
  exact contains_sound (homogeneous_enclosed CA1_2_13I2R8Value CA1_2_13I2R8MassTerm_sound CA1_2_13I2R8Entropy_sound) (by decide +kernel)
lemma CA1_2_13I2R9Raw_sound (a : PairSlot) :
    (CA1_2_13I2R9Raw a).Encloses (CA1_2_13I2R9Value a) := by
  exact residualBall_sound_on (below (shape 1 2 13)) A1_2_13Law (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_2_13Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 2 13) (show (shape 1 2 13) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 9 a
lemma CA1_2_13I2R9Certificates_valid :
    CA1_2_13I2R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA1_2_13I2R9P_check : ∀ a : PairSlot, contains (CA1_2_13I2R9Raw a) (CA1_2_13I2R9P a) = true := by
  decide +kernel
lemma CA1_2_13I2R9P_sound (a : PairSlot) :
    (CA1_2_13I2R9P a).Encloses (CA1_2_13I2R9Value a) :=
  contains_sound (CA1_2_13I2R9Raw_sound a) (CA1_2_13I2R9P_check a)
lemma CA1_2_13I2R9Terms_sound (a : PairSlot) :
    (CA1_2_13I2R9Terms a).Encloses (Foundation.entropyTerm (CA1_2_13I2R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_2_13I2R9Certificates_valid
    (CA1_2_13I2R9CertificateIndex a) (CA1_2_13I2R9P_sound a)
lemma CA1_2_13I2R9Entropy_sound : CA1_2_13I2R9Entropy.Encloses (Foundation.finiteEntropy CA1_2_13I2R9Value) := by
  exact contains_sound (entropyPair_enclosed CA1_2_13I2R9Value CA1_2_13I2R9Terms CA1_2_13I2R9Terms_sound) (by decide +kernel)
lemma CA1_2_13I2R9Mass_sound : CA1_2_13I2R9Mass.Encloses (∑ a, CA1_2_13I2R9Value a) := by
  exact contains_sound (pairSumBall_sound CA1_2_13I2R9P CA1_2_13I2R9Value CA1_2_13I2R9P_sound) (by decide +kernel)
lemma CA1_2_13I2R9MassTerm_sound : CA1_2_13I2R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_2_13I2R9Value a))) :=
  entropyTerm_zero_ball (CA1_2_13I2R9Mass_sound)
lemma CA1_2_13I2R9H_sound : CA1_2_13I2R9H.Encloses (homogeneousEntropy CA1_2_13I2R9Value) := by
  exact contains_sound (homogeneous_enclosed CA1_2_13I2R9Value CA1_2_13I2R9MassTerm_sound CA1_2_13I2R9Entropy_sound) (by decide +kernel)
lemma CA1_2_13I2R10Raw_sound (a : PairSlot) :
    (CA1_2_13I2R10Raw a).Encloses (CA1_2_13I2R10Value a) := by
  exact residualBall_sound_on (below (shape 1 2 13)) A1_2_13Law (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_2_13Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 2 13) (show (shape 1 2 13) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 10 a
lemma CA1_2_13I2R10Certificates_valid :
    CA1_2_13I2R10Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA1_2_13I2R10P_check : ∀ a : PairSlot, contains (CA1_2_13I2R10Raw a) (CA1_2_13I2R10P a) = true := by
  decide +kernel
lemma CA1_2_13I2R10P_sound (a : PairSlot) :
    (CA1_2_13I2R10P a).Encloses (CA1_2_13I2R10Value a) :=
  contains_sound (CA1_2_13I2R10Raw_sound a) (CA1_2_13I2R10P_check a)
lemma CA1_2_13I2R10Terms_sound (a : PairSlot) :
    (CA1_2_13I2R10Terms a).Encloses (Foundation.entropyTerm (CA1_2_13I2R10Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_2_13I2R10Certificates_valid
    (CA1_2_13I2R10CertificateIndex a) (CA1_2_13I2R10P_sound a)
lemma CA1_2_13I2R10Entropy_sound : CA1_2_13I2R10Entropy.Encloses (Foundation.finiteEntropy CA1_2_13I2R10Value) := by
  exact contains_sound (entropyPair_enclosed CA1_2_13I2R10Value CA1_2_13I2R10Terms CA1_2_13I2R10Terms_sound) (by decide +kernel)
lemma CA1_2_13I2R10Mass_sound : CA1_2_13I2R10Mass.Encloses (∑ a, CA1_2_13I2R10Value a) := by
  exact contains_sound (pairSumBall_sound CA1_2_13I2R10P CA1_2_13I2R10Value CA1_2_13I2R10P_sound) (by decide +kernel)
lemma CA1_2_13I2R10MassTerm_sound : CA1_2_13I2R10MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_2_13I2R10Value a))) :=
  entropyTerm_zero_ball (CA1_2_13I2R10Mass_sound)
lemma CA1_2_13I2R10H_sound : CA1_2_13I2R10H.Encloses (homogeneousEntropy CA1_2_13I2R10Value) := by
  exact contains_sound (homogeneous_enclosed CA1_2_13I2R10Value CA1_2_13I2R10MassTerm_sound CA1_2_13I2R10Entropy_sound) (by decide +kernel)
lemma CA1_2_13I2R11Raw_sound (a : PairSlot) :
    (CA1_2_13I2R11Raw a).Encloses (CA1_2_13I2R11Value a) := by
  exact residualBall_sound_on (below (shape 1 2 13)) A1_2_13Law (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_2_13Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 2 13) (show (shape 1 2 13) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 11 a
lemma CA1_2_13I2R11Certificates_valid :
    CA1_2_13I2R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA1_2_13I2R11P_check : ∀ a : PairSlot, contains (CA1_2_13I2R11Raw a) (CA1_2_13I2R11P a) = true := by
  decide +kernel
lemma CA1_2_13I2R11P_sound (a : PairSlot) :
    (CA1_2_13I2R11P a).Encloses (CA1_2_13I2R11Value a) :=
  contains_sound (CA1_2_13I2R11Raw_sound a) (CA1_2_13I2R11P_check a)
lemma CA1_2_13I2R11Terms_sound (a : PairSlot) :
    (CA1_2_13I2R11Terms a).Encloses (Foundation.entropyTerm (CA1_2_13I2R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_2_13I2R11Certificates_valid
    (CA1_2_13I2R11CertificateIndex a) (CA1_2_13I2R11P_sound a)
lemma CA1_2_13I2R11Entropy_sound : CA1_2_13I2R11Entropy.Encloses (Foundation.finiteEntropy CA1_2_13I2R11Value) := by
  exact contains_sound (entropyPair_enclosed CA1_2_13I2R11Value CA1_2_13I2R11Terms CA1_2_13I2R11Terms_sound) (by decide +kernel)
lemma CA1_2_13I2R11Mass_sound : CA1_2_13I2R11Mass.Encloses (∑ a, CA1_2_13I2R11Value a) := by
  exact contains_sound (pairSumBall_sound CA1_2_13I2R11P CA1_2_13I2R11Value CA1_2_13I2R11P_sound) (by decide +kernel)
lemma CA1_2_13I2R11MassTerm_sound : CA1_2_13I2R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_2_13I2R11Value a))) :=
  entropyTerm_zero_ball (CA1_2_13I2R11Mass_sound)
lemma CA1_2_13I2R11H_sound : CA1_2_13I2R11H.Encloses (homogeneousEntropy CA1_2_13I2R11Value) := by
  exact contains_sound (homogeneous_enclosed CA1_2_13I2R11Value CA1_2_13I2R11MassTerm_sound CA1_2_13I2R11Entropy_sound) (by decide +kernel)
lemma CA1_2_13I2R12Raw_sound (a : PairSlot) :
    (CA1_2_13I2R12Raw a).Encloses (CA1_2_13I2R12Value a) := by
  exact residualBall_sound_on (below (shape 1 2 13)) A1_2_13Law (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_2_13Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 2 13) (show (shape 1 2 13) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 12 a
lemma CA1_2_13I2R12Certificates_valid :
    CA1_2_13I2R12Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA1_2_13I2R12P_check : ∀ a : PairSlot, contains (CA1_2_13I2R12Raw a) (CA1_2_13I2R12P a) = true := by
  decide +kernel
lemma CA1_2_13I2R12P_sound (a : PairSlot) :
    (CA1_2_13I2R12P a).Encloses (CA1_2_13I2R12Value a) :=
  contains_sound (CA1_2_13I2R12Raw_sound a) (CA1_2_13I2R12P_check a)
lemma CA1_2_13I2R12Terms_sound (a : PairSlot) :
    (CA1_2_13I2R12Terms a).Encloses (Foundation.entropyTerm (CA1_2_13I2R12Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_2_13I2R12Certificates_valid
    (CA1_2_13I2R12CertificateIndex a) (CA1_2_13I2R12P_sound a)
lemma CA1_2_13I2R12Entropy_sound : CA1_2_13I2R12Entropy.Encloses (Foundation.finiteEntropy CA1_2_13I2R12Value) := by
  exact contains_sound (entropyPair_enclosed CA1_2_13I2R12Value CA1_2_13I2R12Terms CA1_2_13I2R12Terms_sound) (by decide +kernel)
lemma CA1_2_13I2R12Mass_sound : CA1_2_13I2R12Mass.Encloses (∑ a, CA1_2_13I2R12Value a) := by
  exact contains_sound (pairSumBall_sound CA1_2_13I2R12P CA1_2_13I2R12Value CA1_2_13I2R12P_sound) (by decide +kernel)
lemma CA1_2_13I2R12MassTerm_sound : CA1_2_13I2R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_2_13I2R12Value a))) :=
  entropyTerm_zero_ball (CA1_2_13I2R12Mass_sound)
lemma CA1_2_13I2R12H_sound : CA1_2_13I2R12H.Encloses (homogeneousEntropy CA1_2_13I2R12Value) := by
  exact contains_sound (homogeneous_enclosed CA1_2_13I2R12Value CA1_2_13I2R12MassTerm_sound CA1_2_13I2R12Entropy_sound) (by decide +kernel)
lemma CA1_2_13I2R13Raw_sound (a : PairSlot) :
    (CA1_2_13I2R13Raw a).Encloses (CA1_2_13I2R13Value a) := by
  exact residualBall_sound_on (below (shape 1 2 13)) A1_2_13Law (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_2_13Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 2 13) (show (shape 1 2 13) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 13 a
lemma CA1_2_13I2R13Certificates_valid :
    CA1_2_13I2R13Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA1_2_13I2R13P_check : ∀ a : PairSlot, contains (CA1_2_13I2R13Raw a) (CA1_2_13I2R13P a) = true := by
  decide +kernel
lemma CA1_2_13I2R13P_sound (a : PairSlot) :
    (CA1_2_13I2R13P a).Encloses (CA1_2_13I2R13Value a) :=
  contains_sound (CA1_2_13I2R13Raw_sound a) (CA1_2_13I2R13P_check a)
lemma CA1_2_13I2R13Terms_sound (a : PairSlot) :
    (CA1_2_13I2R13Terms a).Encloses (Foundation.entropyTerm (CA1_2_13I2R13Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_2_13I2R13Certificates_valid
    (CA1_2_13I2R13CertificateIndex a) (CA1_2_13I2R13P_sound a)
lemma CA1_2_13I2R13Entropy_sound : CA1_2_13I2R13Entropy.Encloses (Foundation.finiteEntropy CA1_2_13I2R13Value) := by
  exact contains_sound (entropyPair_enclosed CA1_2_13I2R13Value CA1_2_13I2R13Terms CA1_2_13I2R13Terms_sound) (by decide +kernel)
lemma CA1_2_13I2R13Mass_sound : CA1_2_13I2R13Mass.Encloses (∑ a, CA1_2_13I2R13Value a) := by
  exact contains_sound (pairSumBall_sound CA1_2_13I2R13P CA1_2_13I2R13Value CA1_2_13I2R13P_sound) (by decide +kernel)
lemma CA1_2_13I2R13MassTerm_sound : CA1_2_13I2R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_2_13I2R13Value a))) :=
  entropyTerm_zero_ball (CA1_2_13I2R13Mass_sound)
lemma CA1_2_13I2R13H_sound : CA1_2_13I2R13H.Encloses (homogeneousEntropy CA1_2_13I2R13Value) := by
  exact contains_sound (homogeneous_enclosed CA1_2_13I2R13Value CA1_2_13I2R13MassTerm_sound CA1_2_13I2R13Entropy_sound) (by decide +kernel)
lemma CA1_2_13I2R14Raw_sound (a : PairSlot) :
    (CA1_2_13I2R14Raw a).Encloses (CA1_2_13I2R14Value a) := by
  exact residualBall_sound_on (below (shape 1 2 13)) A1_2_13Law (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_2_13Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 2 13) (show (shape 1 2 13) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 14 a
lemma CA1_2_13I2R14Certificates_valid :
    CA1_2_13I2R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA1_2_13I2R14P_check : ∀ a : PairSlot, contains (CA1_2_13I2R14Raw a) (CA1_2_13I2R14P a) = true := by
  decide +kernel
lemma CA1_2_13I2R14P_sound (a : PairSlot) :
    (CA1_2_13I2R14P a).Encloses (CA1_2_13I2R14Value a) :=
  contains_sound (CA1_2_13I2R14Raw_sound a) (CA1_2_13I2R14P_check a)
lemma CA1_2_13I2R14Terms_sound (a : PairSlot) :
    (CA1_2_13I2R14Terms a).Encloses (Foundation.entropyTerm (CA1_2_13I2R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_2_13I2R14Certificates_valid
    (CA1_2_13I2R14CertificateIndex a) (CA1_2_13I2R14P_sound a)
lemma CA1_2_13I2R14Entropy_sound : CA1_2_13I2R14Entropy.Encloses (Foundation.finiteEntropy CA1_2_13I2R14Value) := by
  exact contains_sound (entropyPair_enclosed CA1_2_13I2R14Value CA1_2_13I2R14Terms CA1_2_13I2R14Terms_sound) (by decide +kernel)
lemma CA1_2_13I2R14Mass_sound : CA1_2_13I2R14Mass.Encloses (∑ a, CA1_2_13I2R14Value a) := by
  exact contains_sound (pairSumBall_sound CA1_2_13I2R14P CA1_2_13I2R14Value CA1_2_13I2R14P_sound) (by decide +kernel)
lemma CA1_2_13I2R14MassTerm_sound : CA1_2_13I2R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_2_13I2R14Value a))) :=
  entropyTerm_zero_ball (CA1_2_13I2R14Mass_sound)
lemma CA1_2_13I2R14H_sound : CA1_2_13I2R14H.Encloses (homogeneousEntropy CA1_2_13I2R14Value) := by
  exact contains_sound (homogeneous_enclosed CA1_2_13I2R14Value CA1_2_13I2R14MassTerm_sound CA1_2_13I2R14Entropy_sound) (by decide +kernel)
lemma CA1_2_13I2R15Raw_sound (a : PairSlot) :
    (CA1_2_13I2R15Raw a).Encloses (CA1_2_13I2R15Value a) := by
  exact residualBall_sound_on (below (shape 1 2 13)) A1_2_13Law (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_2_13Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 2 13) (show (shape 1 2 13) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 15 a
lemma CA1_2_13I2R15Certificates_valid :
    CA1_2_13I2R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA1_2_13I2R15P_check : ∀ a : PairSlot, contains (CA1_2_13I2R15Raw a) (CA1_2_13I2R15P a) = true := by
  decide +kernel
lemma CA1_2_13I2R15P_sound (a : PairSlot) :
    (CA1_2_13I2R15P a).Encloses (CA1_2_13I2R15Value a) :=
  contains_sound (CA1_2_13I2R15Raw_sound a) (CA1_2_13I2R15P_check a)
lemma CA1_2_13I2R15Terms_sound (a : PairSlot) :
    (CA1_2_13I2R15Terms a).Encloses (Foundation.entropyTerm (CA1_2_13I2R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_2_13I2R15Certificates_valid
    (CA1_2_13I2R15CertificateIndex a) (CA1_2_13I2R15P_sound a)
lemma CA1_2_13I2R15Entropy_sound : CA1_2_13I2R15Entropy.Encloses (Foundation.finiteEntropy CA1_2_13I2R15Value) := by
  exact contains_sound (entropyPair_enclosed CA1_2_13I2R15Value CA1_2_13I2R15Terms CA1_2_13I2R15Terms_sound) (by decide +kernel)
lemma CA1_2_13I2R15Mass_sound : CA1_2_13I2R15Mass.Encloses (∑ a, CA1_2_13I2R15Value a) := by
  exact contains_sound (pairSumBall_sound CA1_2_13I2R15P CA1_2_13I2R15Value CA1_2_13I2R15P_sound) (by decide +kernel)
lemma CA1_2_13I2R15MassTerm_sound : CA1_2_13I2R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_2_13I2R15Value a))) :=
  entropyTerm_zero_ball (CA1_2_13I2R15Mass_sound)
lemma CA1_2_13I2R15H_sound : CA1_2_13I2R15H.Encloses (homogeneousEntropy CA1_2_13I2R15Value) := by
  exact contains_sound (homogeneous_enclosed CA1_2_13I2R15Value CA1_2_13I2R15MassTerm_sound CA1_2_13I2R15Entropy_sound) (by decide +kernel)
lemma CA1_2_13I2R16Raw_sound (a : PairSlot) :
    (CA1_2_13I2R16Raw a).Encloses (CA1_2_13I2R16Value a) := by
  exact residualBall_sound_on (below (shape 1 2 13)) A1_2_13Law (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_2_13Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 2 13) (show (shape 1 2 13) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 16 a
lemma CA1_2_13I2R16Certificates_valid :
    CA1_2_13I2R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA1_2_13I2R16P_check : ∀ a : PairSlot, contains (CA1_2_13I2R16Raw a) (CA1_2_13I2R16P a) = true := by
  decide +kernel
lemma CA1_2_13I2R16P_sound (a : PairSlot) :
    (CA1_2_13I2R16P a).Encloses (CA1_2_13I2R16Value a) :=
  contains_sound (CA1_2_13I2R16Raw_sound a) (CA1_2_13I2R16P_check a)
lemma CA1_2_13I2R16Terms_sound (a : PairSlot) :
    (CA1_2_13I2R16Terms a).Encloses (Foundation.entropyTerm (CA1_2_13I2R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_2_13I2R16Certificates_valid
    (CA1_2_13I2R16CertificateIndex a) (CA1_2_13I2R16P_sound a)
lemma CA1_2_13I2R16Entropy_sound : CA1_2_13I2R16Entropy.Encloses (Foundation.finiteEntropy CA1_2_13I2R16Value) := by
  exact contains_sound (entropyPair_enclosed CA1_2_13I2R16Value CA1_2_13I2R16Terms CA1_2_13I2R16Terms_sound) (by decide +kernel)
lemma CA1_2_13I2R16Mass_sound : CA1_2_13I2R16Mass.Encloses (∑ a, CA1_2_13I2R16Value a) := by
  exact contains_sound (pairSumBall_sound CA1_2_13I2R16P CA1_2_13I2R16Value CA1_2_13I2R16P_sound) (by decide +kernel)
lemma CA1_2_13I2R16MassTerm_sound : CA1_2_13I2R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_2_13I2R16Value a))) :=
  entropyTerm_zero_ball (CA1_2_13I2R16Mass_sound)
lemma CA1_2_13I2R16H_sound : CA1_2_13I2R16H.Encloses (homogeneousEntropy CA1_2_13I2R16Value) := by
  exact contains_sound (homogeneous_enclosed CA1_2_13I2R16Value CA1_2_13I2R16MassTerm_sound CA1_2_13I2R16Entropy_sound) (by decide +kernel)
lemma CA1_2_13I2ResidualEntropies_sound_oai (k : Fin 17) :
    (CA1_2_13I2ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) k)) := by
  fin_cases k
  · exact CA1_2_13I2R0H_sound
  · exact CA1_2_13I2R1H_sound
  · exact CA1_2_13I2R2H_sound
  · exact CA1_2_13I2R3H_sound
  · exact CA1_2_13I2R4H_sound
  · exact CA1_2_13I2R5H_sound
  · exact CA1_2_13I2R6H_sound
  · exact CA1_2_13I2R7H_sound
  · exact CA1_2_13I2R8H_sound
  · exact CA1_2_13I2R9H_sound
  · exact CA1_2_13I2R10H_sound
  · exact CA1_2_13I2R11H_sound
  · exact CA1_2_13I2R12H_sound
  · exact CA1_2_13I2R13H_sound
  · exact CA1_2_13I2R14H_sound
  · exact CA1_2_13I2R15H_sound
  · exact CA1_2_13I2R16H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_2_13I2ResidualEntropies_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_2_13I2ResidualEntropies_sound_oai
