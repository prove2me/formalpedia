-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_6_6I2PairH_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:27:19.950862+00:00
-- url     : https://prove2.me/submissions/2935c81e-b3f9-4dfe-bcf3-0a79c3a49a05

import Mathlib
import Definitions.Def_OAIQ254M010
import Definitions.Def_OAIQ254M011
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkLog_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_finSumBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_CompactCertificate_entropyLookup_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA4_6_6I2PairCertificates_valid
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA4_6_6I2PairP_sound
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
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA4_6_6I2Pair
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
lemma CA4_6_6I2PairTerms_sound (a : PairSlot × PairSlot) :
    (CA4_6_6I2PairTerms a).Encloses (Foundation.entropyTerm (CA4_6_6I2PairValue a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_6_6I2PairCertificates_valid
    (CA4_6_6I2PairCertificateIndex a) (CA4_6_6I2PairP_sound a)
lemma CA4_6_6I2PairEntropy_sound : CA4_6_6I2PairEntropy.Encloses (Foundation.finiteEntropy CA4_6_6I2PairValue) := by
  exact contains_sound (entropyDoublePair_enclosed CA4_6_6I2PairValue CA4_6_6I2PairTerms CA4_6_6I2PairTerms_sound) (by decide +kernel)
lemma CA4_6_6I2PairMass_sound : CA4_6_6I2PairMass.Encloses (∑ a, CA4_6_6I2PairValue a) := by
  exact contains_sound (doublePairSumBall_sound CA4_6_6I2PairP CA4_6_6I2PairValue CA4_6_6I2PairP_sound) (by decide +kernel)
lemma CA4_6_6I2PairMassTermLog_sound : CA4_6_6I2PairMassTermLog.Encloses (Real.log ((∑ a, CA4_6_6I2PairValue a))) := by
  exact checkLog_sound logTwoBall_sound (CA4_6_6I2PairMass_sound) (w := CA4_6_6I2PairMassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CA4_6_6I2PairMassTerm_sound : CA4_6_6I2PairMassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_6_6I2PairValue a))) := by
  exact contains_sound (entropyTerm_ball (CA4_6_6I2PairMass_sound) CA4_6_6I2PairMassTermLog_sound) (by decide +kernel)
lemma CA4_6_6I2PairH_sound_oai : CA4_6_6I2PairH.Encloses (homogeneousEntropy CA4_6_6I2PairValue) := by
  exact contains_sound (homogeneous_enclosed CA4_6_6I2PairValue CA4_6_6I2PairMassTerm_sound CA4_6_6I2PairEntropy_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_6_6I2PairH_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_6_6I2PairH_sound_oai
