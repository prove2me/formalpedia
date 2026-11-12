-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_3_12I2PairH_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:45:04.689762+00:00
-- url     : https://prove2.me/submissions/3ec60fab-56aa-4c73-97c7-6c3dde2ecc98

import Mathlib
import Definitions.Def_OAIQ254M006
import Definitions.Def_OAIQ254M007
import Definitions.Def_OAIQ254M010
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

lemma forall_fin6 {P : Fin 6 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2)
    (h3 : P 3) (h4 : P 4) (h5 : P 5) : ∀ i, P i := by
  intro i
  fin_cases i <;> assumption

lemma pairSumBall_sound (bs : PairSlot → Ball) (v : PairSlot → ℝ)
    (h : ∀ a, (bs a).Encloses (v a)) :
    (pairSumBall bs).Encloses (∑ a, v a) := by
  exact product_fin6_enclosed _ _ (fun i j => h (i,j))

lemma doublePairSumBall_sound (bs : PairSlot × PairSlot → Ball)
    (v : PairSlot × PairSlot → ℝ) (h : ∀ a, (bs a).Encloses (v a)) :
    (doublePairSumBall bs).Encloses (∑ a, v a) := by
  rw [Fintype.sum_prod_type]
  exact pairSumBall_sound _ _ (fun i => pairSumBall_sound _ _ (fun j => h (i,j)))

lemma entropyDoublePair_enclosed (p : PairSlot × PairSlot → ℝ)
    (bs : PairSlot × PairSlot → Ball)
    (h : ∀ i, (bs i).Encloses (Foundation.entropyTerm (p i))) :
    (doublePairSumBall bs).Encloses (Foundation.finiteEntropy p) :=
  doublePairSumBall_sound _ _ h

lemma homogeneous_enclosed {A : Type*} [Fintype A] (p : A → ℝ)
    {b e : Ball} (hb : b.Encloses (Foundation.entropyTerm (∑ a, p a)))
    (he : e.Encloses (Foundation.finiteEntropy p)) :
    (Ball.add (Ball.neg b) e).Encloses (homogeneousEntropy p) := by
  convert Ball.add_sound (Ball.neg_sound hb) he using 1
  all_goals try with_reducible_and_instances rfl
  simp only [homogeneousEntropy, Foundation.entropyTerm, neg_mul, neg_neg]

lemma pairLawBall_sound_on {A : Type*} [Fintype A] (support : List Shape) (s : Shape)
    (bs : Shape → Ball) (p : Shape → ℝ) (bq : Shape → A → Ball) (q : Shape → A → ℝ)
    (hp : ∀ u ∈ support, (bs u).Encloses (p u))
    (hq : ∀ u ∈ support, ∀ a, (bq u a).Encloses (q u a))
    (hcq : ∀ u ∈ support, ∀ a, (bq (complement s u) a).Encloses (q (complement s u) a))
    (ij : A × A) :
    (pairLawBall support s bs bq ij).Encloses (pairLaw support s p q ij) := by
  apply listSumBall_sound
  intro u hu
  exact Ball.mul_sound (Ball.mul_sound (hp u hu) (hq u hu ij.1)) (hcq u hu ij.2)

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

lemma sparseTripleBall_eq (a b c : Ball) :
    sparseTripleBall a b c = .mul (.mul a b) c := by
  unfold sparseTripleBall
  split_ifs with h
  · rcases h with h | h
    · subst b
      cases a
      cases c
      simp [Ball.mul, Ball.exact]
    · subst c
      cases a
      cases b
      simp [Ball.mul, Ball.exact]
  · rfl

lemma sparsePairLawBall_eq {A : Type*} (support : List Shape) (s : Shape)
    (p : Shape → Ball) (q : Shape → A → Ball) (ij : A × A) :
    sparsePairLawBall support s p q ij = pairLawBall support s p q ij := by
  simp only [sparsePairLawBall, sparseTripleBall_eq, pairLawBall]

lemma sparsePairLawBall_sound_on {A : Type*} [Fintype A] (support : List Shape) (s : Shape)
    (bs : Shape → Ball) (p : Shape → ℝ) (bq : Shape → A → Ball) (q : Shape → A → ℝ)
    (hp : ∀ u ∈ support, (bs u).Encloses (p u))
    (hq : ∀ u ∈ support, ∀ a, (bq u a).Encloses (q u a))
    (hcq : ∀ u ∈ support, ∀ a, (bq (complement s u) a).Encloses (q (complement s u) a))
    (ij : A × A) :
    (sparsePairLawBall support s bs bq ij).Encloses (pairLaw support s p q ij) := by
  rw [sparsePairLawBall_eq]
  exact pairLawBall_sound_on support s bs p bq q hp hq hcq ij

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
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SupportedContraction
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

lemma halfTable_degree_zero_0 : ∀ t ∈ shapes 8, ∀ ij : PairSlot,
    pairDegree ij ≠ t 0 → halfTable t 0 ij = .exact 0 := by
  decide +kernel
lemma halfTable_degree_zero_1 : ∀ t ∈ shapes 8, ∀ ij : PairSlot,
    pairDegree ij ≠ t 1 → halfTable t 1 ij = .exact 0 := by
  decide +kernel
lemma halfTable_degree_zero_2 : ∀ t ∈ shapes 8, ∀ ij : PairSlot,
    pairDegree ij ≠ t 2 → halfTable t 2 ij = .exact 0 := by
  decide +kernel

lemma halfTable_degree_zero (t : Shape) (ht : t ∈ shapes 8) (w : Fin 3)
    (ij : PairSlot) (h : pairDegree ij ≠ t w) : halfTable t w ij = .exact 0 := by
  fin_cases w
  · exact halfTable_degree_zero_0 t ht ij h
  · exact halfTable_degree_zero_1 t ht ij h
  · exact halfTable_degree_zero_2 t ht ij h

lemma listSumBall_eq_zero {A : Type*} (xs : List A) (b : A → Ball)
    (h : ∀ x ∈ xs, b x = .exact 0) : listSumBall xs b = .exact 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change Ball.add (b x) (listSumBall xs b) = .exact 0
    rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]
    decide +kernel

lemma stageAPairBall_zero (s : Shape) (hs : s ∈ positiveInitial) (bs : Shape → Ball)
    (w : Fin 3) (ij : PairSlot × PairSlot)
    (h : pairDegree ij.1 + pairDegree ij.2 ≠ s w) :
    sparsePairLawBall (below s) s bs (fun u => halfTable u w) ij = .exact 0 := by
  apply listSumBall_eq_zero
  intro u hu
  have hc := stageA_support_complement s hs u hu
  by_cases hl : pairDegree ij.1 = u w
  · have hr : pairDegree ij.2 ≠ (complement s u) w := by
      simp only [complement]
      have hu_le := hc.2 w
      omega
    have hz := halfTable_degree_zero (complement s u)
      (stageA_children_size s hs _ hc.1) w ij.2 hr
    simp only [sparseTripleBall, hz, or_true, ite_true, if_true]
  · have hz := halfTable_degree_zero u (stageA_children_size s hs u hu) w ij.1 hl
    simp only [sparseTripleBall, hz, true_or, ite_true, if_true]

lemma stageAPairBall_eq (s : Shape) (hs : s ∈ positiveInitial) (bs : Shape → Ball)
    (w : Fin 3) (ij : PairSlot × PairSlot) :
    stageAPairBall s bs w ij =
      sparsePairLawBall (below s) s bs (fun u => halfTable u w) ij := by
  unfold stageAPairBall
  split_ifs with h
  · rfl
  · exact (stageAPairBall_zero s hs bs w ij h).symm

lemma stageAPairBall_sound (s : Shape) (hs : s ∈ positiveInitial)
    (bs : Shape → Ball) (p : Shape → ℝ)
    (hp : ∀ u ∈ below s, (bs u).Encloses (p u)) (w : Fin 3) (ij : PairSlot × PairSlot) :
    (stageAPairBall s bs w ij).Encloses
      (pairLaw (below s) s p (fun u a => (halfLaw u w a : ℝ)) ij) := by
  rw [stageAPairBall_eq s hs]
  exact sparsePairLawBall_sound_on (below s) s bs p (fun u => halfTable u w)
    (fun u a => (halfLaw u w a : ℝ)) hp
    (fun u hu a => halfTable_sound u (stageA_children_size s hs u hu) w a)
    (fun u hu a => halfTable_sound (complement s u)
      (stageA_children_size s hs _ (stageA_support_complement s hs u hu).1) w a) ij

end MatrixMultiplication.NativeNumerics

end
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
lemma CA1_3_12I2PairRaw_sound (a : PairSlot × PairSlot) :
    (CA1_3_12I2PairRaw a).Encloses (CA1_3_12I2PairValue a) := by
  exact stageAPairBall_sound (shape 1 3 12) (by decide +kernel) A1_3_12Law (fun u => (stageALaw (shape 1 3 12) u : ℝ)) (fun u _ => A1_3_12Law_sound u) 2 a
lemma CA1_3_12I2PairCertificates_valid :
    CA1_3_12I2PairCertificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA1_3_12I2PairP_check_0_0 : ∀ k l : Fin 6, contains (CA1_3_12I2PairRaw ((0,0),(k,l))) (CA1_3_12I2PairP ((0,0),(k,l))) = true := by
  decide +kernel
lemma CA1_3_12I2PairP_check_0_1 : ∀ k l : Fin 6, contains (CA1_3_12I2PairRaw ((0,1),(k,l))) (CA1_3_12I2PairP ((0,1),(k,l))) = true := by
  decide +kernel
lemma CA1_3_12I2PairP_check_0_2 : ∀ k l : Fin 6, contains (CA1_3_12I2PairRaw ((0,2),(k,l))) (CA1_3_12I2PairP ((0,2),(k,l))) = true := by
  decide +kernel
lemma CA1_3_12I2PairP_check_0_3 : ∀ k l : Fin 6, contains (CA1_3_12I2PairRaw ((0,3),(k,l))) (CA1_3_12I2PairP ((0,3),(k,l))) = true := by
  decide +kernel
lemma CA1_3_12I2PairP_check_0_4 : ∀ k l : Fin 6, contains (CA1_3_12I2PairRaw ((0,4),(k,l))) (CA1_3_12I2PairP ((0,4),(k,l))) = true := by
  decide +kernel
lemma CA1_3_12I2PairP_check_0_5 : ∀ k l : Fin 6, contains (CA1_3_12I2PairRaw ((0,5),(k,l))) (CA1_3_12I2PairP ((0,5),(k,l))) = true := by
  decide +kernel
lemma CA1_3_12I2PairP_check_1_0 : ∀ k l : Fin 6, contains (CA1_3_12I2PairRaw ((1,0),(k,l))) (CA1_3_12I2PairP ((1,0),(k,l))) = true := by
  decide +kernel
lemma CA1_3_12I2PairP_check_1_1 : ∀ k l : Fin 6, contains (CA1_3_12I2PairRaw ((1,1),(k,l))) (CA1_3_12I2PairP ((1,1),(k,l))) = true := by
  decide +kernel
lemma CA1_3_12I2PairP_check_1_2 : ∀ k l : Fin 6, contains (CA1_3_12I2PairRaw ((1,2),(k,l))) (CA1_3_12I2PairP ((1,2),(k,l))) = true := by
  decide +kernel
lemma CA1_3_12I2PairP_check_1_3 : ∀ k l : Fin 6, contains (CA1_3_12I2PairRaw ((1,3),(k,l))) (CA1_3_12I2PairP ((1,3),(k,l))) = true := by
  decide +kernel
lemma CA1_3_12I2PairP_check_1_4 : ∀ k l : Fin 6, contains (CA1_3_12I2PairRaw ((1,4),(k,l))) (CA1_3_12I2PairP ((1,4),(k,l))) = true := by
  decide +kernel
lemma CA1_3_12I2PairP_check_1_5 : ∀ k l : Fin 6, contains (CA1_3_12I2PairRaw ((1,5),(k,l))) (CA1_3_12I2PairP ((1,5),(k,l))) = true := by
  decide +kernel
lemma CA1_3_12I2PairP_check_2_0 : ∀ k l : Fin 6, contains (CA1_3_12I2PairRaw ((2,0),(k,l))) (CA1_3_12I2PairP ((2,0),(k,l))) = true := by
  decide +kernel
lemma CA1_3_12I2PairP_check_2_1 : ∀ k l : Fin 6, contains (CA1_3_12I2PairRaw ((2,1),(k,l))) (CA1_3_12I2PairP ((2,1),(k,l))) = true := by
  decide +kernel
lemma CA1_3_12I2PairP_check_2_2 : ∀ k l : Fin 6, contains (CA1_3_12I2PairRaw ((2,2),(k,l))) (CA1_3_12I2PairP ((2,2),(k,l))) = true := by
  decide +kernel
lemma CA1_3_12I2PairP_check_2_3 : ∀ k l : Fin 6, contains (CA1_3_12I2PairRaw ((2,3),(k,l))) (CA1_3_12I2PairP ((2,3),(k,l))) = true := by
  decide +kernel
lemma CA1_3_12I2PairP_check_2_4 : ∀ k l : Fin 6, contains (CA1_3_12I2PairRaw ((2,4),(k,l))) (CA1_3_12I2PairP ((2,4),(k,l))) = true := by
  decide +kernel
lemma CA1_3_12I2PairP_check_2_5 : ∀ k l : Fin 6, contains (CA1_3_12I2PairRaw ((2,5),(k,l))) (CA1_3_12I2PairP ((2,5),(k,l))) = true := by
  decide +kernel
lemma CA1_3_12I2PairP_check_3_0 : ∀ k l : Fin 6, contains (CA1_3_12I2PairRaw ((3,0),(k,l))) (CA1_3_12I2PairP ((3,0),(k,l))) = true := by
  decide +kernel
lemma CA1_3_12I2PairP_check_3_1 : ∀ k l : Fin 6, contains (CA1_3_12I2PairRaw ((3,1),(k,l))) (CA1_3_12I2PairP ((3,1),(k,l))) = true := by
  decide +kernel
lemma CA1_3_12I2PairP_check_3_2 : ∀ k l : Fin 6, contains (CA1_3_12I2PairRaw ((3,2),(k,l))) (CA1_3_12I2PairP ((3,2),(k,l))) = true := by
  decide +kernel
lemma CA1_3_12I2PairP_check_3_3 : ∀ k l : Fin 6, contains (CA1_3_12I2PairRaw ((3,3),(k,l))) (CA1_3_12I2PairP ((3,3),(k,l))) = true := by
  decide +kernel
lemma CA1_3_12I2PairP_check_3_4 : ∀ k l : Fin 6, contains (CA1_3_12I2PairRaw ((3,4),(k,l))) (CA1_3_12I2PairP ((3,4),(k,l))) = true := by
  decide +kernel
lemma CA1_3_12I2PairP_check_3_5 : ∀ k l : Fin 6, contains (CA1_3_12I2PairRaw ((3,5),(k,l))) (CA1_3_12I2PairP ((3,5),(k,l))) = true := by
  decide +kernel
lemma CA1_3_12I2PairP_check_4_0 : ∀ k l : Fin 6, contains (CA1_3_12I2PairRaw ((4,0),(k,l))) (CA1_3_12I2PairP ((4,0),(k,l))) = true := by
  decide +kernel
lemma CA1_3_12I2PairP_check_4_1 : ∀ k l : Fin 6, contains (CA1_3_12I2PairRaw ((4,1),(k,l))) (CA1_3_12I2PairP ((4,1),(k,l))) = true := by
  decide +kernel
lemma CA1_3_12I2PairP_check_4_2 : ∀ k l : Fin 6, contains (CA1_3_12I2PairRaw ((4,2),(k,l))) (CA1_3_12I2PairP ((4,2),(k,l))) = true := by
  decide +kernel
lemma CA1_3_12I2PairP_check_4_3 : ∀ k l : Fin 6, contains (CA1_3_12I2PairRaw ((4,3),(k,l))) (CA1_3_12I2PairP ((4,3),(k,l))) = true := by
  decide +kernel
lemma CA1_3_12I2PairP_check_4_4 : ∀ k l : Fin 6, contains (CA1_3_12I2PairRaw ((4,4),(k,l))) (CA1_3_12I2PairP ((4,4),(k,l))) = true := by
  decide +kernel
lemma CA1_3_12I2PairP_check_4_5 : ∀ k l : Fin 6, contains (CA1_3_12I2PairRaw ((4,5),(k,l))) (CA1_3_12I2PairP ((4,5),(k,l))) = true := by
  decide +kernel
lemma CA1_3_12I2PairP_check_5_0 : ∀ k l : Fin 6, contains (CA1_3_12I2PairRaw ((5,0),(k,l))) (CA1_3_12I2PairP ((5,0),(k,l))) = true := by
  decide +kernel
lemma CA1_3_12I2PairP_check_5_1 : ∀ k l : Fin 6, contains (CA1_3_12I2PairRaw ((5,1),(k,l))) (CA1_3_12I2PairP ((5,1),(k,l))) = true := by
  decide +kernel
lemma CA1_3_12I2PairP_check_5_2 : ∀ k l : Fin 6, contains (CA1_3_12I2PairRaw ((5,2),(k,l))) (CA1_3_12I2PairP ((5,2),(k,l))) = true := by
  decide +kernel
lemma CA1_3_12I2PairP_check_5_3 : ∀ k l : Fin 6, contains (CA1_3_12I2PairRaw ((5,3),(k,l))) (CA1_3_12I2PairP ((5,3),(k,l))) = true := by
  decide +kernel
lemma CA1_3_12I2PairP_check_5_4 : ∀ k l : Fin 6, contains (CA1_3_12I2PairRaw ((5,4),(k,l))) (CA1_3_12I2PairP ((5,4),(k,l))) = true := by
  decide +kernel
lemma CA1_3_12I2PairP_check_5_5 : ∀ k l : Fin 6, contains (CA1_3_12I2PairRaw ((5,5),(k,l))) (CA1_3_12I2PairP ((5,5),(k,l))) = true := by
  decide +kernel
lemma CA1_3_12I2PairP_check (a : PairSlot × PairSlot) : contains (CA1_3_12I2PairRaw a) (CA1_3_12I2PairP a) = true := by
  rcases a with ⟨⟨i,j⟩,⟨k,l⟩⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (CA1_3_12I2PairP_check_0_0 k l) (CA1_3_12I2PairP_check_0_1 k l) (CA1_3_12I2PairP_check_0_2 k l) (CA1_3_12I2PairP_check_0_3 k l) (CA1_3_12I2PairP_check_0_4 k l) (CA1_3_12I2PairP_check_0_5 k l)
  · exact forall_fin6 (CA1_3_12I2PairP_check_1_0 k l) (CA1_3_12I2PairP_check_1_1 k l) (CA1_3_12I2PairP_check_1_2 k l) (CA1_3_12I2PairP_check_1_3 k l) (CA1_3_12I2PairP_check_1_4 k l) (CA1_3_12I2PairP_check_1_5 k l)
  · exact forall_fin6 (CA1_3_12I2PairP_check_2_0 k l) (CA1_3_12I2PairP_check_2_1 k l) (CA1_3_12I2PairP_check_2_2 k l) (CA1_3_12I2PairP_check_2_3 k l) (CA1_3_12I2PairP_check_2_4 k l) (CA1_3_12I2PairP_check_2_5 k l)
  · exact forall_fin6 (CA1_3_12I2PairP_check_3_0 k l) (CA1_3_12I2PairP_check_3_1 k l) (CA1_3_12I2PairP_check_3_2 k l) (CA1_3_12I2PairP_check_3_3 k l) (CA1_3_12I2PairP_check_3_4 k l) (CA1_3_12I2PairP_check_3_5 k l)
  · exact forall_fin6 (CA1_3_12I2PairP_check_4_0 k l) (CA1_3_12I2PairP_check_4_1 k l) (CA1_3_12I2PairP_check_4_2 k l) (CA1_3_12I2PairP_check_4_3 k l) (CA1_3_12I2PairP_check_4_4 k l) (CA1_3_12I2PairP_check_4_5 k l)
  · exact forall_fin6 (CA1_3_12I2PairP_check_5_0 k l) (CA1_3_12I2PairP_check_5_1 k l) (CA1_3_12I2PairP_check_5_2 k l) (CA1_3_12I2PairP_check_5_3 k l) (CA1_3_12I2PairP_check_5_4 k l) (CA1_3_12I2PairP_check_5_5 k l)
lemma CA1_3_12I2PairP_sound (a : PairSlot × PairSlot) :
    (CA1_3_12I2PairP a).Encloses (CA1_3_12I2PairValue a) :=
  contains_sound (CA1_3_12I2PairRaw_sound a) (CA1_3_12I2PairP_check a)
lemma CA1_3_12I2PairTerms_sound (a : PairSlot × PairSlot) :
    (CA1_3_12I2PairTerms a).Encloses (Foundation.entropyTerm (CA1_3_12I2PairValue a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_3_12I2PairCertificates_valid
    (CA1_3_12I2PairCertificateIndex a) (CA1_3_12I2PairP_sound a)
lemma CA1_3_12I2PairEntropy_sound : CA1_3_12I2PairEntropy.Encloses (Foundation.finiteEntropy CA1_3_12I2PairValue) := by
  exact contains_sound (entropyDoublePair_enclosed CA1_3_12I2PairValue CA1_3_12I2PairTerms CA1_3_12I2PairTerms_sound) (by decide +kernel)
lemma CA1_3_12I2PairMass_sound : CA1_3_12I2PairMass.Encloses (∑ a, CA1_3_12I2PairValue a) := by
  exact contains_sound (doublePairSumBall_sound CA1_3_12I2PairP CA1_3_12I2PairValue CA1_3_12I2PairP_sound) (by decide +kernel)
lemma CA1_3_12I2PairMassTermLog_sound : CA1_3_12I2PairMassTermLog.Encloses (Real.log ((∑ a, CA1_3_12I2PairValue a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_3_12I2PairMass_sound) (w := CA1_3_12I2PairMassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CA1_3_12I2PairMassTerm_sound : CA1_3_12I2PairMassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_3_12I2PairValue a))) := by
  exact contains_sound (entropyTerm_ball (CA1_3_12I2PairMass_sound) CA1_3_12I2PairMassTermLog_sound) (by decide +kernel)
lemma CA1_3_12I2PairH_sound_oai : CA1_3_12I2PairH.Encloses (homogeneousEntropy CA1_3_12I2PairValue) := by
  exact contains_sound (homogeneous_enclosed CA1_3_12I2PairValue CA1_3_12I2PairMassTerm_sound CA1_3_12I2PairEntropy_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_3_12I2PairH_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_3_12I2PairH_sound_oai
