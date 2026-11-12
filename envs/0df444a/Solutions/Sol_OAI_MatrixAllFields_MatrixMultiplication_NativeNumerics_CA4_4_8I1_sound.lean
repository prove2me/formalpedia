-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_4_8I1_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:25:30.338629+00:00
-- url     : https://prove2.me/submissions/09edf00d-879a-4bb4-b1c7-697b506184c8

import Mathlib
import Definitions.Def_OAIQ254M011
import Definitions.Def_OAIQ254M012
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_mul_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkLog_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_finSumBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_CompactCertificate_entropyLookup_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_A4_4_8Law_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA4_4_8I1Group_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_entropyDoublePair_enclosed
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_entropyTerm_ball
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_homogeneous_enclosed
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_stageAPairBall_sound

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

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA4_4_8I1
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
lemma CA4_4_8I1PairRaw_sound (a : PairSlot × PairSlot) :
    (CA4_4_8I1PairRaw a).Encloses (CA4_4_8I1PairValue a) := by
  exact stageAPairBall_sound (shape 4 4 8) (by decide +kernel) A4_4_8Law (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (fun u _ => A4_4_8Law_sound u) 1 a
lemma CA4_4_8I1PairCertificates_valid :
    CA4_4_8I1PairCertificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA4_4_8I1PairP_check_0_0 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((0,0),(k,l))) (CA4_4_8I1PairP ((0,0),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_0_1 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((0,1),(k,l))) (CA4_4_8I1PairP ((0,1),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_0_2 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((0,2),(k,l))) (CA4_4_8I1PairP ((0,2),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_0_3 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((0,3),(k,l))) (CA4_4_8I1PairP ((0,3),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_0_4 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((0,4),(k,l))) (CA4_4_8I1PairP ((0,4),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_0_5 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((0,5),(k,l))) (CA4_4_8I1PairP ((0,5),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_1_0 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((1,0),(k,l))) (CA4_4_8I1PairP ((1,0),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_1_1 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((1,1),(k,l))) (CA4_4_8I1PairP ((1,1),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_1_2 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((1,2),(k,l))) (CA4_4_8I1PairP ((1,2),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_1_3 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((1,3),(k,l))) (CA4_4_8I1PairP ((1,3),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_1_4 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((1,4),(k,l))) (CA4_4_8I1PairP ((1,4),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_1_5 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((1,5),(k,l))) (CA4_4_8I1PairP ((1,5),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_2_0 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((2,0),(k,l))) (CA4_4_8I1PairP ((2,0),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_2_1 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((2,1),(k,l))) (CA4_4_8I1PairP ((2,1),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_2_2 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((2,2),(k,l))) (CA4_4_8I1PairP ((2,2),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_2_3 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((2,3),(k,l))) (CA4_4_8I1PairP ((2,3),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_2_4 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((2,4),(k,l))) (CA4_4_8I1PairP ((2,4),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_2_5 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((2,5),(k,l))) (CA4_4_8I1PairP ((2,5),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_3_0 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((3,0),(k,l))) (CA4_4_8I1PairP ((3,0),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_3_1 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((3,1),(k,l))) (CA4_4_8I1PairP ((3,1),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_3_2 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((3,2),(k,l))) (CA4_4_8I1PairP ((3,2),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_3_3 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((3,3),(k,l))) (CA4_4_8I1PairP ((3,3),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_3_4 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((3,4),(k,l))) (CA4_4_8I1PairP ((3,4),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_3_5 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((3,5),(k,l))) (CA4_4_8I1PairP ((3,5),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_4_0 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((4,0),(k,l))) (CA4_4_8I1PairP ((4,0),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_4_1 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((4,1),(k,l))) (CA4_4_8I1PairP ((4,1),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_4_2 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((4,2),(k,l))) (CA4_4_8I1PairP ((4,2),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_4_3 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((4,3),(k,l))) (CA4_4_8I1PairP ((4,3),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_4_4 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((4,4),(k,l))) (CA4_4_8I1PairP ((4,4),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_4_5 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((4,5),(k,l))) (CA4_4_8I1PairP ((4,5),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_5_0 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((5,0),(k,l))) (CA4_4_8I1PairP ((5,0),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_5_1 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((5,1),(k,l))) (CA4_4_8I1PairP ((5,1),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_5_2 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((5,2),(k,l))) (CA4_4_8I1PairP ((5,2),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_5_3 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((5,3),(k,l))) (CA4_4_8I1PairP ((5,3),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_5_4 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((5,4),(k,l))) (CA4_4_8I1PairP ((5,4),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check_5_5 : ∀ k l : Fin 6, contains (CA4_4_8I1PairRaw ((5,5),(k,l))) (CA4_4_8I1PairP ((5,5),(k,l))) = true := by
  decide +kernel
lemma CA4_4_8I1PairP_check (a : PairSlot × PairSlot) : contains (CA4_4_8I1PairRaw a) (CA4_4_8I1PairP a) = true := by
  rcases a with ⟨⟨i,j⟩,⟨k,l⟩⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (CA4_4_8I1PairP_check_0_0 k l) (CA4_4_8I1PairP_check_0_1 k l) (CA4_4_8I1PairP_check_0_2 k l) (CA4_4_8I1PairP_check_0_3 k l) (CA4_4_8I1PairP_check_0_4 k l) (CA4_4_8I1PairP_check_0_5 k l)
  · exact forall_fin6 (CA4_4_8I1PairP_check_1_0 k l) (CA4_4_8I1PairP_check_1_1 k l) (CA4_4_8I1PairP_check_1_2 k l) (CA4_4_8I1PairP_check_1_3 k l) (CA4_4_8I1PairP_check_1_4 k l) (CA4_4_8I1PairP_check_1_5 k l)
  · exact forall_fin6 (CA4_4_8I1PairP_check_2_0 k l) (CA4_4_8I1PairP_check_2_1 k l) (CA4_4_8I1PairP_check_2_2 k l) (CA4_4_8I1PairP_check_2_3 k l) (CA4_4_8I1PairP_check_2_4 k l) (CA4_4_8I1PairP_check_2_5 k l)
  · exact forall_fin6 (CA4_4_8I1PairP_check_3_0 k l) (CA4_4_8I1PairP_check_3_1 k l) (CA4_4_8I1PairP_check_3_2 k l) (CA4_4_8I1PairP_check_3_3 k l) (CA4_4_8I1PairP_check_3_4 k l) (CA4_4_8I1PairP_check_3_5 k l)
  · exact forall_fin6 (CA4_4_8I1PairP_check_4_0 k l) (CA4_4_8I1PairP_check_4_1 k l) (CA4_4_8I1PairP_check_4_2 k l) (CA4_4_8I1PairP_check_4_3 k l) (CA4_4_8I1PairP_check_4_4 k l) (CA4_4_8I1PairP_check_4_5 k l)
  · exact forall_fin6 (CA4_4_8I1PairP_check_5_0 k l) (CA4_4_8I1PairP_check_5_1 k l) (CA4_4_8I1PairP_check_5_2 k l) (CA4_4_8I1PairP_check_5_3 k l) (CA4_4_8I1PairP_check_5_4 k l) (CA4_4_8I1PairP_check_5_5 k l)
lemma CA4_4_8I1PairP_sound (a : PairSlot × PairSlot) :
    (CA4_4_8I1PairP a).Encloses (CA4_4_8I1PairValue a) :=
  contains_sound (CA4_4_8I1PairRaw_sound a) (CA4_4_8I1PairP_check a)
lemma CA4_4_8I1PairTerms_sound (a : PairSlot × PairSlot) :
    (CA4_4_8I1PairTerms a).Encloses (Foundation.entropyTerm (CA4_4_8I1PairValue a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_4_8I1PairCertificates_valid
    (CA4_4_8I1PairCertificateIndex a) (CA4_4_8I1PairP_sound a)
lemma CA4_4_8I1PairEntropy_sound : CA4_4_8I1PairEntropy.Encloses (Foundation.finiteEntropy CA4_4_8I1PairValue) := by
  exact contains_sound (entropyDoublePair_enclosed CA4_4_8I1PairValue CA4_4_8I1PairTerms CA4_4_8I1PairTerms_sound) (by decide +kernel)
lemma CA4_4_8I1PairMass_sound : CA4_4_8I1PairMass.Encloses (∑ a, CA4_4_8I1PairValue a) := by
  exact contains_sound (doublePairSumBall_sound CA4_4_8I1PairP CA4_4_8I1PairValue CA4_4_8I1PairP_sound) (by decide +kernel)
lemma CA4_4_8I1PairMassTermLog_sound : CA4_4_8I1PairMassTermLog.Encloses (Real.log ((∑ a, CA4_4_8I1PairValue a))) := by
  exact checkLog_sound logTwoBall_sound (CA4_4_8I1PairMass_sound) (w := CA4_4_8I1PairMassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CA4_4_8I1PairMassTerm_sound : CA4_4_8I1PairMassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_4_8I1PairValue a))) := by
  exact contains_sound (entropyTerm_ball (CA4_4_8I1PairMass_sound) CA4_4_8I1PairMassTermLog_sound) (by decide +kernel)
lemma CA4_4_8I1PairH_sound : CA4_4_8I1PairH.Encloses (homogeneousEntropy CA4_4_8I1PairValue) := by
  exact contains_sound (homogeneous_enclosed CA4_4_8I1PairValue CA4_4_8I1PairMassTerm_sound CA4_4_8I1PairEntropy_sound) (by decide +kernel)

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
lemma CA4_4_8I1_sound_oai : CA4_4_8I1H.Encloses (stageACapacity (shape 4 4 8) 1) := by
  have hb := contains_sound (Ball.add_sound CA4_4_8I1PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CA4_4_8I1Group_sound)))
    (show contains (.add CA4_4_8I1PairH (.neg (.mul (.exact 2) CA4_4_8I1Group))) CA4_4_8I1H = true by decide +kernel)
  unfold CA4_4_8I1PairValue at hb
  simpa only [stageACapacity, nativeCapacity,
    show (1 : Fin 3) ≠ 0 by decide, ite_false, if_false, sub_eq_add_neg] using hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_4_8I1_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_4_8I1_sound_oai
