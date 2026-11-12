-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z0_6_2H2Entropy_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T14:54:42.286217+00:00
-- url     : https://prove2.me/submissions/959dec59-42bf-4a6c-bc8e-7aaca8dd4bf7

import Mathlib
import Definitions.Def_OAIQ254M007
import Definitions.Def_OAIQ254M011
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkLog_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_finSumBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_Z0_6_2Probs_sound
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

end Ball

end MatrixMultiplication.AllFieldCertificates

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
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitB1_1_6
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
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
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
lemma Z0_6_2Half_sound (w : Fin 3) (ij : PairSlot) :
    (Z0_6_2Half w ij).Encloses (halfLaw (shape 0 6 2) w ij : ℝ) := by
  have hp : positive (shape 0 6 2) = false := by decide +kernel
  simp only [Z0_6_2Half, halfLaw, hp, Bool.false_eq_true, ite_false, if_false]
  split_ifs
  · exact Ball.exact_sound 1
  · exact Ball.exact_sound 0
  · exact Z0_6_2Probs_sound _
  · exact Z0_6_2Probs_sound _

lemma Z0_6_2H2E_2_0Log_sound : Z0_6_2H2E_2_0Log.Encloses (Real.log (Z0_6_2H2Value ((2,0) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z0_6_2Half_sound 2) ((2,0) : PairSlot)) (w := Z0_6_2H2E_2_0LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z0_6_2H2E_2_0_sound : Z0_6_2H2E_2_0.Encloses (Foundation.entropyTerm (Z0_6_2H2Value ((2,0) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z0_6_2Half_sound 2) ((2,0) : PairSlot)) Z0_6_2H2E_2_0Log_sound) (by decide +kernel)
lemma Z0_6_2H2E_3_0Log_sound : Z0_6_2H2E_3_0Log.Encloses (Real.log (Z0_6_2H2Value ((3,0) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z0_6_2Half_sound 2) ((3,0) : PairSlot)) (w := Z0_6_2H2E_3_0LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z0_6_2H2E_3_0_sound : Z0_6_2H2E_3_0.Encloses (Foundation.entropyTerm (Z0_6_2H2Value ((3,0) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z0_6_2Half_sound 2) ((3,0) : PairSlot)) Z0_6_2H2E_3_0Log_sound) (by decide +kernel)
lemma Z0_6_2H2E_1_1Log_sound : Z0_6_2H2E_1_1Log.Encloses (Real.log (Z0_6_2H2Value ((1,1) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z0_6_2Half_sound 2) ((1,1) : PairSlot)) (w := Z0_6_2H2E_1_1LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z0_6_2H2E_1_1_sound : Z0_6_2H2E_1_1.Encloses (Foundation.entropyTerm (Z0_6_2H2Value ((1,1) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z0_6_2Half_sound 2) ((1,1) : PairSlot)) Z0_6_2H2E_1_1Log_sound) (by decide +kernel)
lemma Z0_6_2H2E_0_2Log_sound : Z0_6_2H2E_0_2Log.Encloses (Real.log (Z0_6_2H2Value ((0,2) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z0_6_2Half_sound 2) ((0,2) : PairSlot)) (w := Z0_6_2H2E_0_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z0_6_2H2E_0_2_sound : Z0_6_2H2E_0_2.Encloses (Foundation.entropyTerm (Z0_6_2H2Value ((0,2) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z0_6_2Half_sound 2) ((0,2) : PairSlot)) Z0_6_2H2E_0_2Log_sound) (by decide +kernel)
lemma Z0_6_2H2E_0_3Log_sound : Z0_6_2H2E_0_3Log.Encloses (Real.log (Z0_6_2H2Value ((0,3) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z0_6_2Half_sound 2) ((0,3) : PairSlot)) (w := Z0_6_2H2E_0_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z0_6_2H2E_0_3_sound : Z0_6_2H2E_0_3.Encloses (Foundation.entropyTerm (Z0_6_2H2Value ((0,3) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z0_6_2Half_sound 2) ((0,3) : PairSlot)) Z0_6_2H2E_0_3Log_sound) (by decide +kernel)
lemma Z0_6_2H2Terms_sound (a : PairSlot) :
    (Z0_6_2H2Terms a).Encloses (Foundation.entropyTerm (Z0_6_2H2Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_6_2Half_sound 2) ((0,0) : PairSlot))) (entropyTerm_zero_ball ((Z0_6_2Half_sound 2) ((0,1) : PairSlot))) Z0_6_2H2E_0_2_sound Z0_6_2H2E_0_3_sound (entropyTerm_zero_ball ((Z0_6_2Half_sound 2) ((0,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_6_2Half_sound 2) ((0,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_6_2Half_sound 2) ((1,0) : PairSlot))) Z0_6_2H2E_1_1_sound (entropyTerm_zero_ball ((Z0_6_2Half_sound 2) ((1,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_6_2Half_sound 2) ((1,3) : PairSlot))) (entropyTerm_zero_ball ((Z0_6_2Half_sound 2) ((1,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_6_2Half_sound 2) ((1,5) : PairSlot)))
  · exact forall_fin6 Z0_6_2H2E_2_0_sound (entropyTerm_zero_ball ((Z0_6_2Half_sound 2) ((2,1) : PairSlot))) (entropyTerm_zero_ball ((Z0_6_2Half_sound 2) ((2,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_6_2Half_sound 2) ((2,3) : PairSlot))) (entropyTerm_zero_ball ((Z0_6_2Half_sound 2) ((2,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_6_2Half_sound 2) ((2,5) : PairSlot)))
  · exact forall_fin6 Z0_6_2H2E_3_0_sound (entropyTerm_zero_ball ((Z0_6_2Half_sound 2) ((3,1) : PairSlot))) (entropyTerm_zero_ball ((Z0_6_2Half_sound 2) ((3,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_6_2Half_sound 2) ((3,3) : PairSlot))) (entropyTerm_zero_ball ((Z0_6_2Half_sound 2) ((3,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_6_2Half_sound 2) ((3,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_6_2Half_sound 2) ((4,0) : PairSlot))) (entropyTerm_zero_ball ((Z0_6_2Half_sound 2) ((4,1) : PairSlot))) (entropyTerm_zero_ball ((Z0_6_2Half_sound 2) ((4,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_6_2Half_sound 2) ((4,3) : PairSlot))) (entropyTerm_zero_ball ((Z0_6_2Half_sound 2) ((4,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_6_2Half_sound 2) ((4,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_6_2Half_sound 2) ((5,0) : PairSlot))) (entropyTerm_zero_ball ((Z0_6_2Half_sound 2) ((5,1) : PairSlot))) (entropyTerm_zero_ball ((Z0_6_2Half_sound 2) ((5,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_6_2Half_sound 2) ((5,3) : PairSlot))) (entropyTerm_zero_ball ((Z0_6_2Half_sound 2) ((5,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_6_2Half_sound 2) ((5,5) : PairSlot)))
lemma Z0_6_2H2Entropy_sound_oai : Z0_6_2H2Entropy.Encloses (Foundation.finiteEntropy Z0_6_2H2Value) := by
  exact contains_sound (entropyPair_enclosed Z0_6_2H2Value Z0_6_2H2Terms Z0_6_2H2Terms_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z0_6_2H2Entropy_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z0_6_2H2Entropy_sound_oai
