-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z2_0_6Four_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:22:09.853859+00:00
-- url     : https://prove2.me/submissions/f92ae89c-6761-4fc4-a714-efc974e8549a

import Mathlib
import Definitions.Def_OAIQ254M011
import Definitions.Def_OAIQ254M012
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_mul_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkLog_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_finSumBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_Z2_0_6Probs_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_entropyTerm_ball
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_multLogs_sound

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
lemma Z2_0_6E_2_5Log_sound : Z2_0_6E_2_5Log.Encloses (Real.log (Z2_0_6Value ((2,5) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z2_0_6Probs_sound ((2,5) : PairSlot)) (w := Z2_0_6E_2_5LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z2_0_6E_2_5_sound : Z2_0_6E_2_5.Encloses (Foundation.entropyTerm (Z2_0_6Value ((2,5) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z2_0_6Probs_sound ((2,5) : PairSlot)) Z2_0_6E_2_5Log_sound) (by decide +kernel)
lemma Z2_0_6E_3_5Log_sound : Z2_0_6E_3_5Log.Encloses (Real.log (Z2_0_6Value ((3,5) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z2_0_6Probs_sound ((3,5) : PairSlot)) (w := Z2_0_6E_3_5LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z2_0_6E_3_5_sound : Z2_0_6E_3_5.Encloses (Foundation.entropyTerm (Z2_0_6Value ((3,5) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z2_0_6Probs_sound ((3,5) : PairSlot)) Z2_0_6E_3_5Log_sound) (by decide +kernel)
lemma Z2_0_6E_4_4Log_sound : Z2_0_6E_4_4Log.Encloses (Real.log (Z2_0_6Value ((4,4) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z2_0_6Probs_sound ((4,4) : PairSlot)) (w := Z2_0_6E_4_4LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z2_0_6E_4_4_sound : Z2_0_6E_4_4.Encloses (Foundation.entropyTerm (Z2_0_6Value ((4,4) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z2_0_6Probs_sound ((4,4) : PairSlot)) Z2_0_6E_4_4Log_sound) (by decide +kernel)
lemma Z2_0_6E_5_2Log_sound : Z2_0_6E_5_2Log.Encloses (Real.log (Z2_0_6Value ((5,2) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z2_0_6Probs_sound ((5,2) : PairSlot)) (w := Z2_0_6E_5_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z2_0_6E_5_2_sound : Z2_0_6E_5_2.Encloses (Foundation.entropyTerm (Z2_0_6Value ((5,2) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z2_0_6Probs_sound ((5,2) : PairSlot)) Z2_0_6E_5_2Log_sound) (by decide +kernel)
lemma Z2_0_6E_5_3Log_sound : Z2_0_6E_5_3Log.Encloses (Real.log (Z2_0_6Value ((5,3) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z2_0_6Probs_sound ((5,3) : PairSlot)) (w := Z2_0_6E_5_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma Z2_0_6E_5_3_sound : Z2_0_6E_5_3.Encloses (Foundation.entropyTerm (Z2_0_6Value ((5,3) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z2_0_6Probs_sound ((5,3) : PairSlot)) Z2_0_6E_5_3Log_sound) (by decide +kernel)
lemma Z2_0_6Terms_sound (a : PairSlot) :
    (Z2_0_6Terms a).Encloses (Foundation.entropyTerm (Z2_0_6Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (entropyTerm_zero_ball (Z2_0_6Probs_sound ((0,0) : PairSlot))) (entropyTerm_zero_ball (Z2_0_6Probs_sound ((0,1) : PairSlot))) (entropyTerm_zero_ball (Z2_0_6Probs_sound ((0,2) : PairSlot))) (entropyTerm_zero_ball (Z2_0_6Probs_sound ((0,3) : PairSlot))) (entropyTerm_zero_ball (Z2_0_6Probs_sound ((0,4) : PairSlot))) (entropyTerm_zero_ball (Z2_0_6Probs_sound ((0,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z2_0_6Probs_sound ((1,0) : PairSlot))) (entropyTerm_zero_ball (Z2_0_6Probs_sound ((1,1) : PairSlot))) (entropyTerm_zero_ball (Z2_0_6Probs_sound ((1,2) : PairSlot))) (entropyTerm_zero_ball (Z2_0_6Probs_sound ((1,3) : PairSlot))) (entropyTerm_zero_ball (Z2_0_6Probs_sound ((1,4) : PairSlot))) (entropyTerm_zero_ball (Z2_0_6Probs_sound ((1,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z2_0_6Probs_sound ((2,0) : PairSlot))) (entropyTerm_zero_ball (Z2_0_6Probs_sound ((2,1) : PairSlot))) (entropyTerm_zero_ball (Z2_0_6Probs_sound ((2,2) : PairSlot))) (entropyTerm_zero_ball (Z2_0_6Probs_sound ((2,3) : PairSlot))) (entropyTerm_zero_ball (Z2_0_6Probs_sound ((2,4) : PairSlot))) Z2_0_6E_2_5_sound
  · exact forall_fin6 (entropyTerm_zero_ball (Z2_0_6Probs_sound ((3,0) : PairSlot))) (entropyTerm_zero_ball (Z2_0_6Probs_sound ((3,1) : PairSlot))) (entropyTerm_zero_ball (Z2_0_6Probs_sound ((3,2) : PairSlot))) (entropyTerm_zero_ball (Z2_0_6Probs_sound ((3,3) : PairSlot))) (entropyTerm_zero_ball (Z2_0_6Probs_sound ((3,4) : PairSlot))) Z2_0_6E_3_5_sound
  · exact forall_fin6 (entropyTerm_zero_ball (Z2_0_6Probs_sound ((4,0) : PairSlot))) (entropyTerm_zero_ball (Z2_0_6Probs_sound ((4,1) : PairSlot))) (entropyTerm_zero_ball (Z2_0_6Probs_sound ((4,2) : PairSlot))) (entropyTerm_zero_ball (Z2_0_6Probs_sound ((4,3) : PairSlot))) Z2_0_6E_4_4_sound (entropyTerm_zero_ball (Z2_0_6Probs_sound ((4,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z2_0_6Probs_sound ((5,0) : PairSlot))) (entropyTerm_zero_ball (Z2_0_6Probs_sound ((5,1) : PairSlot))) Z2_0_6E_5_2_sound Z2_0_6E_5_3_sound (entropyTerm_zero_ball (Z2_0_6Probs_sound ((5,4) : PairSlot))) (entropyTerm_zero_ball (Z2_0_6Probs_sound ((5,5) : PairSlot)))
lemma Z2_0_6Entropy_sound : Z2_0_6Entropy.Encloses (Foundation.finiteEntropy Z2_0_6Value) := by
  exact contains_sound (entropyPair_enclosed Z2_0_6Value Z2_0_6Terms Z2_0_6Terms_sound) (by decide +kernel)
lemma Z2_0_6Labels_sound : Z2_0_6Labels.Encloses
    (∑ a : PairSlot, (zeroPairLaw (shape 2 0 6) a.1 a.2 : ℝ) *
      Real.log (AllFieldParameters.multiplicity a.1 * AllFieldParameters.multiplicity a.2 : ℕ)) := by
  exact contains_sound (pairSumBall_sound (fun a => .mul (Z2_0_6Probs a) (multLogs a))
    _ (fun a => Ball.mul_sound (Z2_0_6Probs_sound a) (multLogs_sound a))) (by decide +kernel)
lemma Z2_0_6Four_sound_oai : Z2_0_6Four.Encloses (AllFieldZeroLeafRates.fourRate (shape 2 0 6)) := by
  exact contains_sound (Ball.add_sound Z2_0_6Entropy_sound Z2_0_6Labels_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z2_0_6Four_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z2_0_6Four_sound_oai
