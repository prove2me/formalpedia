-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z2_0_6H2Entropy_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T14:56:04.316671+00:00
-- url     : https://prove2.me/submissions/6b82f997-9ba2-41fc-9678-c1d827f6a51a

import Mathlib
import Definitions.Def_OAIQ254M011
import Definitions.Def_OAIQ254M012
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkLog_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_Z2_0_6Probs_sound
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

lemma forall_fin6 {P : Fin 6 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2)
    (h3 : P 3) (h4 : P 4) (h5 : P 5) : ∀ i, P i := by
  intro i
  fin_cases i <;> assumption

lemma pairSumBall_sound (bs : PairSlot → Ball) (v : PairSlot → ℝ)
    (h : ∀ a, (bs a).Encloses (v a)) :
    (pairSumBall bs).Encloses (∑ a, v a) := by
  exact product_fin6_enclosed _ _ (fun i j => h (i,j))

lemma entropyPair_enclosed (p : PairSlot → ℝ) (bs : PairSlot → Ball)
    (h : ∀ i, (bs i).Encloses (Foundation.entropyTerm (p i))) :
    (pairSumBall bs).Encloses (Foundation.finiteEntropy p) :=
  pairSumBall_sound _ _ h

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Four2_0_6
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
lemma Z2_0_6Half_sound (w : Fin 3) (ij : PairSlot) :
    (Z2_0_6Half w ij).Encloses (halfLaw (shape 2 0 6) w ij : ℝ) := by
  have hp : positive (shape 2 0 6) = false := by decide +kernel
  simp only [Z2_0_6Half, halfLaw, hp, Bool.false_eq_true, ite_false, if_false]
  split_ifs
  · exact Ball.exact_sound 1
  · exact Ball.exact_sound 0
  · exact Z2_0_6Probs_sound _
  · exact Z2_0_6Probs_sound _

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
lemma Z2_0_6H2E_2_5Log_sound : Z2_0_6H2E_2_5Log.Encloses (Real.log (Z2_0_6H2Value ((2,5) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z2_0_6Half_sound 2) ((2,5) : PairSlot)) (w := Z2_0_6H2E_2_5LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z2_0_6H2E_2_5_sound : Z2_0_6H2E_2_5.Encloses (Foundation.entropyTerm (Z2_0_6H2Value ((2,5) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z2_0_6Half_sound 2) ((2,5) : PairSlot)) Z2_0_6H2E_2_5Log_sound) (by decide +kernel)
lemma Z2_0_6H2E_3_5Log_sound : Z2_0_6H2E_3_5Log.Encloses (Real.log (Z2_0_6H2Value ((3,5) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z2_0_6Half_sound 2) ((3,5) : PairSlot)) (w := Z2_0_6H2E_3_5LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z2_0_6H2E_3_5_sound : Z2_0_6H2E_3_5.Encloses (Foundation.entropyTerm (Z2_0_6H2Value ((3,5) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z2_0_6Half_sound 2) ((3,5) : PairSlot)) Z2_0_6H2E_3_5Log_sound) (by decide +kernel)
lemma Z2_0_6H2E_4_4Log_sound : Z2_0_6H2E_4_4Log.Encloses (Real.log (Z2_0_6H2Value ((4,4) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z2_0_6Half_sound 2) ((4,4) : PairSlot)) (w := Z2_0_6H2E_4_4LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z2_0_6H2E_4_4_sound : Z2_0_6H2E_4_4.Encloses (Foundation.entropyTerm (Z2_0_6H2Value ((4,4) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z2_0_6Half_sound 2) ((4,4) : PairSlot)) Z2_0_6H2E_4_4Log_sound) (by decide +kernel)
lemma Z2_0_6H2E_5_2Log_sound : Z2_0_6H2E_5_2Log.Encloses (Real.log (Z2_0_6H2Value ((5,2) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z2_0_6Half_sound 2) ((5,2) : PairSlot)) (w := Z2_0_6H2E_5_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z2_0_6H2E_5_2_sound : Z2_0_6H2E_5_2.Encloses (Foundation.entropyTerm (Z2_0_6H2Value ((5,2) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z2_0_6Half_sound 2) ((5,2) : PairSlot)) Z2_0_6H2E_5_2Log_sound) (by decide +kernel)
lemma Z2_0_6H2E_5_3Log_sound : Z2_0_6H2E_5_3Log.Encloses (Real.log (Z2_0_6H2Value ((5,3) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z2_0_6Half_sound 2) ((5,3) : PairSlot)) (w := Z2_0_6H2E_5_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z2_0_6H2E_5_3_sound : Z2_0_6H2E_5_3.Encloses (Foundation.entropyTerm (Z2_0_6H2Value ((5,3) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z2_0_6Half_sound 2) ((5,3) : PairSlot)) Z2_0_6H2E_5_3Log_sound) (by decide +kernel)
lemma Z2_0_6H2Terms_sound (a : PairSlot) :
    (Z2_0_6H2Terms a).Encloses (Foundation.entropyTerm (Z2_0_6H2Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((0,0) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((0,1) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((0,2) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((0,3) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((0,4) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((0,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((1,0) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((1,1) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((1,2) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((1,3) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((1,4) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((1,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((2,0) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((2,1) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((2,2) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((2,3) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((2,4) : PairSlot))) Z2_0_6H2E_2_5_sound
  · exact forall_fin6 (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((3,0) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((3,1) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((3,2) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((3,3) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((3,4) : PairSlot))) Z2_0_6H2E_3_5_sound
  · exact forall_fin6 (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((4,0) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((4,1) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((4,2) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((4,3) : PairSlot))) Z2_0_6H2E_4_4_sound (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((4,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((5,0) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((5,1) : PairSlot))) Z2_0_6H2E_5_2_sound Z2_0_6H2E_5_3_sound (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((5,4) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((5,5) : PairSlot)))
lemma Z2_0_6H2Entropy_sound_oai : Z2_0_6H2Entropy.Encloses (Foundation.finiteEntropy Z2_0_6H2Value) := by
  exact contains_sound (entropyPair_enclosed Z2_0_6H2Value Z2_0_6H2Terms Z2_0_6H2Terms_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z2_0_6H2Entropy_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z2_0_6H2Entropy_sound_oai
