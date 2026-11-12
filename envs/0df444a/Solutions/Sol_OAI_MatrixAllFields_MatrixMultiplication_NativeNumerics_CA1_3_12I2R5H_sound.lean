-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_3_12I2R5H_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:46:57.329179+00:00
-- url     : https://prove2.me/submissions/cb877ec7-bee5-46c6-897c-91eec9dc2375

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
lemma w191_sound : w191.Encloses (weight (-1514) : ℝ) := by
  exact weight_enclosed_of_trace (-1514) w191Trace w191S0 w191S1 w191S2 w191S3 w191S4 w191S5
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
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_3_12I2
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
lemma CA1_3_12I2R5Raw_sound (a : PairSlot) :
    (CA1_3_12I2R5Raw a).Encloses (CA1_3_12I2R5Value a) := by
  exact residualBall_sound_on (below (shape 1 3 12)) A1_3_12Law (fun u => (stageALaw (shape 1 3 12) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_3_12Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 3 12) (show (shape 1 3 12) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 5 a
lemma CA1_3_12I2R5Certificates_valid :
    CA1_3_12I2R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA1_3_12I2R5P_check : ∀ a : PairSlot, contains (CA1_3_12I2R5Raw a) (CA1_3_12I2R5P a) = true := by
  decide +kernel
lemma CA1_3_12I2R5P_sound (a : PairSlot) :
    (CA1_3_12I2R5P a).Encloses (CA1_3_12I2R5Value a) :=
  contains_sound (CA1_3_12I2R5Raw_sound a) (CA1_3_12I2R5P_check a)
lemma CA1_3_12I2R5Terms_sound (a : PairSlot) :
    (CA1_3_12I2R5Terms a).Encloses (Foundation.entropyTerm (CA1_3_12I2R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_3_12I2R5Certificates_valid
    (CA1_3_12I2R5CertificateIndex a) (CA1_3_12I2R5P_sound a)
lemma CA1_3_12I2R5Entropy_sound : CA1_3_12I2R5Entropy.Encloses (Foundation.finiteEntropy CA1_3_12I2R5Value) := by
  exact contains_sound (entropyPair_enclosed CA1_3_12I2R5Value CA1_3_12I2R5Terms CA1_3_12I2R5Terms_sound) (by decide +kernel)
lemma CA1_3_12I2R5Mass_sound : CA1_3_12I2R5Mass.Encloses (∑ a, CA1_3_12I2R5Value a) := by
  exact contains_sound (pairSumBall_sound CA1_3_12I2R5P CA1_3_12I2R5Value CA1_3_12I2R5P_sound) (by decide +kernel)
lemma CA1_3_12I2R5MassTermLog_sound : CA1_3_12I2R5MassTermLog.Encloses (Real.log ((∑ a, CA1_3_12I2R5Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_3_12I2R5Mass_sound) (w := CA1_3_12I2R5MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CA1_3_12I2R5MassTerm_sound : CA1_3_12I2R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_3_12I2R5Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_3_12I2R5Mass_sound) CA1_3_12I2R5MassTermLog_sound) (by decide +kernel)
lemma CA1_3_12I2R5H_sound_oai : CA1_3_12I2R5H.Encloses (homogeneousEntropy CA1_3_12I2R5Value) := by
  exact contains_sound (homogeneous_enclosed CA1_3_12I2R5Value CA1_3_12I2R5MassTerm_sound CA1_3_12I2R5Entropy_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_3_12I2R5H_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_3_12I2R5H_sound_oai
