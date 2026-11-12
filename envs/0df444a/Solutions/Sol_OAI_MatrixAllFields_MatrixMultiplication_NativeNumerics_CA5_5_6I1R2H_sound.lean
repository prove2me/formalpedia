-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA5_5_6I1R2H_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T14:19:38.285311+00:00
-- url     : https://prove2.me/submissions/9d98c434-e239-4080-bb34-02a3171359f5

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
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_A5_5_6Law_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_entropyTerm_ball
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_halfTable_sound
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

namespace MatrixMultiplication.AllFieldInitialEntropyCertificate
open AllFieldParameters AllFieldCertificates AllFieldCertificates.Replay
open scoped BigOperators

lemma listSumBall_sound {α : Type*} (xs : List α) (b : α → Ball) (v : α → ℝ)
    (h : ∀ x ∈ xs, (b x).Encloses (v x)) :
    (listSumBall xs b).Encloses ((xs.map v).sum) := by
  induction xs with
  | nil => simpa [listSumBall] using Ball.exact_sound 0
  | cons x xs ih =>
    simpa only [listSumBall, List.foldr_cons, List.map_cons, List.sum_cons] using
      Ball.add_sound (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

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
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA5_5_6I1
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
lemma CA5_5_6I1R2Raw_sound (a : PairSlot) :
    (CA5_5_6I1R2Raw a).Encloses (CA5_5_6I1R2Value a) := by
  exact residualBall_sound_on (below (shape 5 5 6)) A5_5_6Law (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A5_5_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 5 5 6) (show (shape 5 5 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 2 a
lemma CA5_5_6I1R2Certificates_valid :
    CA5_5_6I1R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA5_5_6I1R2P_check : ∀ a : PairSlot, contains (CA5_5_6I1R2Raw a) (CA5_5_6I1R2P a) = true := by
  decide +kernel
lemma CA5_5_6I1R2P_sound (a : PairSlot) :
    (CA5_5_6I1R2P a).Encloses (CA5_5_6I1R2Value a) :=
  contains_sound (CA5_5_6I1R2Raw_sound a) (CA5_5_6I1R2P_check a)
lemma CA5_5_6I1R2Terms_sound (a : PairSlot) :
    (CA5_5_6I1R2Terms a).Encloses (Foundation.entropyTerm (CA5_5_6I1R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA5_5_6I1R2Certificates_valid
    (CA5_5_6I1R2CertificateIndex a) (CA5_5_6I1R2P_sound a)
lemma CA5_5_6I1R2Entropy_sound : CA5_5_6I1R2Entropy.Encloses (Foundation.finiteEntropy CA5_5_6I1R2Value) := by
  exact contains_sound (entropyPair_enclosed CA5_5_6I1R2Value CA5_5_6I1R2Terms CA5_5_6I1R2Terms_sound) (by decide +kernel)
lemma CA5_5_6I1R2Mass_sound : CA5_5_6I1R2Mass.Encloses (∑ a, CA5_5_6I1R2Value a) := by
  exact contains_sound (pairSumBall_sound CA5_5_6I1R2P CA5_5_6I1R2Value CA5_5_6I1R2P_sound) (by decide +kernel)
lemma CA5_5_6I1R2MassTermLog_sound : CA5_5_6I1R2MassTermLog.Encloses (Real.log ((∑ a, CA5_5_6I1R2Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA5_5_6I1R2Mass_sound) (w := CA5_5_6I1R2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CA5_5_6I1R2MassTerm_sound : CA5_5_6I1R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA5_5_6I1R2Value a))) := by
  exact contains_sound (entropyTerm_ball (CA5_5_6I1R2Mass_sound) CA5_5_6I1R2MassTermLog_sound) (by decide +kernel)
lemma CA5_5_6I1R2H_sound_oai : CA5_5_6I1R2H.Encloses (homogeneousEntropy CA5_5_6I1R2Value) := by
  exact contains_sound (homogeneous_enclosed CA5_5_6I1R2Value CA5_5_6I1R2MassTerm_sound CA5_5_6I1R2Entropy_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA5_5_6I1R2H_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA5_5_6I1R2H_sound_oai
