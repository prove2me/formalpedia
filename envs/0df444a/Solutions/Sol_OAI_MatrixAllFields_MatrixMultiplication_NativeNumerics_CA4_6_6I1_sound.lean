-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_6_6I1_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:21:31.174611+00:00
-- url     : https://prove2.me/submissions/bd69e77b-976b-48c9-8d00-08ba2000a42b

import Mathlib
import Definitions.Def_OAIQ254M010
import Definitions.Def_OAIQ254M011
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_mul_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkLog_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_finSumBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_CompactCertificate_entropyLookup_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA4_6_6I1Group_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA4_6_6I1PairP_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_entropyDoublePair_enclosed
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_entropyTerm_ball
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_homogeneous_enclosed

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

end Ball

end MatrixMultiplication.AllFieldCertificates

end

end MatrixAllFields

end OAI
end

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
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA4_6_6I1Pair
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
lemma CA4_6_6I1PairCertificates_valid :
    CA4_6_6I1PairCertificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA4_6_6I1PairTerms_sound (a : PairSlot × PairSlot) :
    (CA4_6_6I1PairTerms a).Encloses (Foundation.entropyTerm (CA4_6_6I1PairValue a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_6_6I1PairCertificates_valid
    (CA4_6_6I1PairCertificateIndex a) (CA4_6_6I1PairP_sound a)
lemma CA4_6_6I1PairEntropy_sound : CA4_6_6I1PairEntropy.Encloses (Foundation.finiteEntropy CA4_6_6I1PairValue) := by
  exact contains_sound (entropyDoublePair_enclosed CA4_6_6I1PairValue CA4_6_6I1PairTerms CA4_6_6I1PairTerms_sound) (by decide +kernel)
lemma CA4_6_6I1PairMass_sound : CA4_6_6I1PairMass.Encloses (∑ a, CA4_6_6I1PairValue a) := by
  exact contains_sound (doublePairSumBall_sound CA4_6_6I1PairP CA4_6_6I1PairValue CA4_6_6I1PairP_sound) (by decide +kernel)
lemma CA4_6_6I1PairMassTermLog_sound : CA4_6_6I1PairMassTermLog.Encloses (Real.log ((∑ a, CA4_6_6I1PairValue a))) := by
  exact checkLog_sound logTwoBall_sound (CA4_6_6I1PairMass_sound) (w := CA4_6_6I1PairMassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CA4_6_6I1PairMassTerm_sound : CA4_6_6I1PairMassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_6_6I1PairValue a))) := by
  exact contains_sound (entropyTerm_ball (CA4_6_6I1PairMass_sound) CA4_6_6I1PairMassTermLog_sound) (by decide +kernel)
lemma CA4_6_6I1PairH_sound : CA4_6_6I1PairH.Encloses (homogeneousEntropy CA4_6_6I1PairValue) := by
  exact contains_sound (homogeneous_enclosed CA4_6_6I1PairValue CA4_6_6I1PairMassTerm_sound CA4_6_6I1PairEntropy_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA4_6_6I1
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
lemma CA4_6_6I1_sound_oai : CA4_6_6I1H.Encloses (stageACapacity (shape 4 6 6) 1) := by
  have hb := contains_sound (Ball.add_sound CA4_6_6I1PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CA4_6_6I1Group_sound)))
    (show contains (.add CA4_6_6I1PairH (.neg (.mul (.exact 2) CA4_6_6I1Group))) CA4_6_6I1H = true by decide +kernel)
  unfold CA4_6_6I1PairValue at hb
  simpa only [stageACapacity, nativeCapacity,
    show (1 : Fin 3) ≠ 0 by decide, ite_false, if_false, sub_eq_add_neg] using hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_6_6I1_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_6_6I1_sound_oai
