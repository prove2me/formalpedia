-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_4_9I2PairH_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:26:43.441097+00:00
-- url     : https://prove2.me/submissions/b1678365-ff10-46e7-9d0c-3626ab804f49

import Mathlib
import Definitions.Def_OAIQ254M009
import Definitions.Def_OAIQ254M011
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkLog_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_finSumBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_CompactCertificate_entropyLookup_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA3_4_9I2PairP_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_entropyDoublePair_enclosed
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_entropyTerm_ball
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_homogeneous_enclosed

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SparseContraction
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
open AllFieldInitialEntropyCertificate
open scoped BigOperators

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

lemma doublePairSumBall_sound (bs : PairSlot × PairSlot → Ball)
    (v : PairSlot × PairSlot → ℝ) (h : ∀ a, (bs a).Encloses (v a)) :
    (doublePairSumBall bs).Encloses (∑ a, v a) := by
  rw [Fintype.sum_prod_type]
  exact pairSumBall_sound _ _ (fun i => pairSumBall_sound _ _ (fun j => h (i,j)))

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA3_4_9I2Pair
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
lemma CA3_4_9I2PairCertificates_valid :
    CA3_4_9I2PairCertificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA3_4_9I2PairTerms_sound (a : PairSlot × PairSlot) :
    (CA3_4_9I2PairTerms a).Encloses (Foundation.entropyTerm (CA3_4_9I2PairValue a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_4_9I2PairCertificates_valid
    (CA3_4_9I2PairCertificateIndex a) (CA3_4_9I2PairP_sound a)
lemma CA3_4_9I2PairEntropy_sound : CA3_4_9I2PairEntropy.Encloses (Foundation.finiteEntropy CA3_4_9I2PairValue) := by
  exact contains_sound (entropyDoublePair_enclosed CA3_4_9I2PairValue CA3_4_9I2PairTerms CA3_4_9I2PairTerms_sound) (by decide +kernel)
lemma CA3_4_9I2PairMass_sound : CA3_4_9I2PairMass.Encloses (∑ a, CA3_4_9I2PairValue a) := by
  exact contains_sound (doublePairSumBall_sound CA3_4_9I2PairP CA3_4_9I2PairValue CA3_4_9I2PairP_sound) (by decide +kernel)
lemma CA3_4_9I2PairMassTermLog_sound : CA3_4_9I2PairMassTermLog.Encloses (Real.log ((∑ a, CA3_4_9I2PairValue a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_4_9I2PairMass_sound) (w := CA3_4_9I2PairMassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CA3_4_9I2PairMassTerm_sound : CA3_4_9I2PairMassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_4_9I2PairValue a))) := by
  exact contains_sound (entropyTerm_ball (CA3_4_9I2PairMass_sound) CA3_4_9I2PairMassTermLog_sound) (by decide +kernel)
lemma CA3_4_9I2PairH_sound_oai : CA3_4_9I2PairH.Encloses (homogeneousEntropy CA3_4_9I2PairValue) := by
  exact contains_sound (homogeneous_enclosed CA3_4_9I2PairValue CA3_4_9I2PairMassTerm_sound CA3_4_9I2PairEntropy_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_4_9I2PairH_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_4_9I2PairH_sound_oai
