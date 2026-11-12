-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I1_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T12:02:31.723699+00:00
-- url     : https://prove2.me/submissions/bb34cfd1-3b77-4c97-9bd1-1efd709c3d25

import Mathlib
import Definitions.Def_OAIQ254M007
import Definitions.Def_OAIQ254M011
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_mul_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkLog_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_CompactCertificate_entropyLookup_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_A1_6_9Law_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_6_9I1PairH_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_6_9I1R10H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_6_9I1R11H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_6_9I1R12H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_6_9I1R13H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_6_9I1R14H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_6_9I1R15H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_6_9I1R16H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_6_9I1R2H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_6_9I1R3H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_6_9I1R4H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_6_9I1R5H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_6_9I1R7H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_6_9I1R8H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_6_9I1R9H_sound
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

lemma singletonBall_sound {A : Type*} [Fintype A] (support : List Shape)
    (bs : Shape → Ball) (p : Shape → ℝ) (priority : Placement) (position : Fin 3)
    (be : Shape → Ball) (q : Shape → A → ℝ)
    (hp : ∀ u ∈ support, (bs u).Encloses (p u))
    (he : ∀ u ∈ support, designated priority position u →
      (be u).Encloses (homogeneousEntropy (q u))) :
    (singletonBall support bs priority position be).Encloses
      (singletonEntropy support p priority position q) := by
  apply listSumBall_sound
  intro u hu
  by_cases hk : designated priority position u
  · simpa only [hk, ite_true, if_true] using Ball.mul_sound (hp u hu) (he u hu hk)
  · simpa only [hk, ite_false, if_false, Rat.cast_zero] using Ball.exact_sound 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitB1_3_4
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

lemma A1_6_9_below : below (shape 1 6 9) = [
  (shape 0 0 8),
  (shape 0 1 7),
  (shape 0 2 6),
  (shape 0 3 5),
  (shape 0 4 4),
  (shape 0 5 3),
  (shape 0 6 2),
  (shape 1 0 7),
  (shape 1 1 6),
  (shape 1 2 5),
  (shape 1 3 4),
  (shape 1 4 3),
  (shape 1 5 2),
  (shape 1 6 1)] := by decide +kernel

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_6_9I1
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
lemma CA1_6_9I1R0Raw_sound (a : PairSlot) :
    (CA1_6_9I1R0Raw a).Encloses (CA1_6_9I1R0Value a) := by
  exact residualBall_sound_on (below (shape 1 6 9)) A1_6_9Law (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_6_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 6 9) (show (shape 1 6 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 0 a
lemma CA1_6_9I1R0Certificates_valid :
    CA1_6_9I1R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA1_6_9I1R0P_check : ∀ a : PairSlot, contains (CA1_6_9I1R0Raw a) (CA1_6_9I1R0P a) = true := by
  decide +kernel
lemma CA1_6_9I1R0P_sound (a : PairSlot) :
    (CA1_6_9I1R0P a).Encloses (CA1_6_9I1R0Value a) :=
  contains_sound (CA1_6_9I1R0Raw_sound a) (CA1_6_9I1R0P_check a)
lemma CA1_6_9I1R0Terms_sound (a : PairSlot) :
    (CA1_6_9I1R0Terms a).Encloses (Foundation.entropyTerm (CA1_6_9I1R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_6_9I1R0Certificates_valid
    (CA1_6_9I1R0CertificateIndex a) (CA1_6_9I1R0P_sound a)
lemma CA1_6_9I1R0Entropy_sound : CA1_6_9I1R0Entropy.Encloses (Foundation.finiteEntropy CA1_6_9I1R0Value) := by
  exact contains_sound (entropyPair_enclosed CA1_6_9I1R0Value CA1_6_9I1R0Terms CA1_6_9I1R0Terms_sound) (by decide +kernel)
lemma CA1_6_9I1R0Mass_sound : CA1_6_9I1R0Mass.Encloses (∑ a, CA1_6_9I1R0Value a) := by
  exact contains_sound (pairSumBall_sound CA1_6_9I1R0P CA1_6_9I1R0Value CA1_6_9I1R0P_sound) (by decide +kernel)
lemma CA1_6_9I1R0MassTermLog_sound : CA1_6_9I1R0MassTermLog.Encloses (Real.log ((∑ a, CA1_6_9I1R0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_6_9I1R0Mass_sound) (w := CA1_6_9I1R0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CA1_6_9I1R0MassTerm_sound : CA1_6_9I1R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_6_9I1R0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_6_9I1R0Mass_sound) CA1_6_9I1R0MassTermLog_sound) (by decide +kernel)
lemma CA1_6_9I1R0H_sound : CA1_6_9I1R0H.Encloses (homogeneousEntropy CA1_6_9I1R0Value) := by
  exact contains_sound (homogeneous_enclosed CA1_6_9I1R0Value CA1_6_9I1R0MassTerm_sound CA1_6_9I1R0Entropy_sound) (by decide +kernel)
lemma CA1_6_9I1R1Raw_sound (a : PairSlot) :
    (CA1_6_9I1R1Raw a).Encloses (CA1_6_9I1R1Value a) := by
  exact residualBall_sound_on (below (shape 1 6 9)) A1_6_9Law (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_6_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 6 9) (show (shape 1 6 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 1 a
lemma CA1_6_9I1R1Certificates_valid :
    CA1_6_9I1R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA1_6_9I1R1P_check : ∀ a : PairSlot, contains (CA1_6_9I1R1Raw a) (CA1_6_9I1R1P a) = true := by
  decide +kernel
lemma CA1_6_9I1R1P_sound (a : PairSlot) :
    (CA1_6_9I1R1P a).Encloses (CA1_6_9I1R1Value a) :=
  contains_sound (CA1_6_9I1R1Raw_sound a) (CA1_6_9I1R1P_check a)
lemma CA1_6_9I1R1Terms_sound (a : PairSlot) :
    (CA1_6_9I1R1Terms a).Encloses (Foundation.entropyTerm (CA1_6_9I1R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_6_9I1R1Certificates_valid
    (CA1_6_9I1R1CertificateIndex a) (CA1_6_9I1R1P_sound a)
lemma CA1_6_9I1R1Entropy_sound : CA1_6_9I1R1Entropy.Encloses (Foundation.finiteEntropy CA1_6_9I1R1Value) := by
  exact contains_sound (entropyPair_enclosed CA1_6_9I1R1Value CA1_6_9I1R1Terms CA1_6_9I1R1Terms_sound) (by decide +kernel)
lemma CA1_6_9I1R1Mass_sound : CA1_6_9I1R1Mass.Encloses (∑ a, CA1_6_9I1R1Value a) := by
  exact contains_sound (pairSumBall_sound CA1_6_9I1R1P CA1_6_9I1R1Value CA1_6_9I1R1P_sound) (by decide +kernel)
lemma CA1_6_9I1R1MassTermLog_sound : CA1_6_9I1R1MassTermLog.Encloses (Real.log ((∑ a, CA1_6_9I1R1Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_6_9I1R1Mass_sound) (w := CA1_6_9I1R1MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CA1_6_9I1R1MassTerm_sound : CA1_6_9I1R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_6_9I1R1Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_6_9I1R1Mass_sound) CA1_6_9I1R1MassTermLog_sound) (by decide +kernel)
lemma CA1_6_9I1R1H_sound : CA1_6_9I1R1H.Encloses (homogeneousEntropy CA1_6_9I1R1Value) := by
  exact contains_sound (homogeneous_enclosed CA1_6_9I1R1Value CA1_6_9I1R1MassTerm_sound CA1_6_9I1R1Entropy_sound) (by decide +kernel)
lemma CA1_6_9I1R6Raw_sound (a : PairSlot) :
    (CA1_6_9I1R6Raw a).Encloses (CA1_6_9I1R6Value a) := by
  exact residualBall_sound_on (below (shape 1 6 9)) A1_6_9Law (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_6_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 6 9) (show (shape 1 6 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 6 a
lemma CA1_6_9I1R6Certificates_valid :
    CA1_6_9I1R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA1_6_9I1R6P_check : ∀ a : PairSlot, contains (CA1_6_9I1R6Raw a) (CA1_6_9I1R6P a) = true := by
  decide +kernel
lemma CA1_6_9I1R6P_sound (a : PairSlot) :
    (CA1_6_9I1R6P a).Encloses (CA1_6_9I1R6Value a) :=
  contains_sound (CA1_6_9I1R6Raw_sound a) (CA1_6_9I1R6P_check a)
lemma CA1_6_9I1R6Terms_sound (a : PairSlot) :
    (CA1_6_9I1R6Terms a).Encloses (Foundation.entropyTerm (CA1_6_9I1R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_6_9I1R6Certificates_valid
    (CA1_6_9I1R6CertificateIndex a) (CA1_6_9I1R6P_sound a)
lemma CA1_6_9I1R6Entropy_sound : CA1_6_9I1R6Entropy.Encloses (Foundation.finiteEntropy CA1_6_9I1R6Value) := by
  exact contains_sound (entropyPair_enclosed CA1_6_9I1R6Value CA1_6_9I1R6Terms CA1_6_9I1R6Terms_sound) (by decide +kernel)
lemma CA1_6_9I1R6Mass_sound : CA1_6_9I1R6Mass.Encloses (∑ a, CA1_6_9I1R6Value a) := by
  exact contains_sound (pairSumBall_sound CA1_6_9I1R6P CA1_6_9I1R6Value CA1_6_9I1R6P_sound) (by decide +kernel)
lemma CA1_6_9I1R6MassTermLog_sound : CA1_6_9I1R6MassTermLog.Encloses (Real.log ((∑ a, CA1_6_9I1R6Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_6_9I1R6Mass_sound) (w := CA1_6_9I1R6MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CA1_6_9I1R6MassTerm_sound : CA1_6_9I1R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_6_9I1R6Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_6_9I1R6Mass_sound) CA1_6_9I1R6MassTermLog_sound) (by decide +kernel)
lemma CA1_6_9I1R6H_sound : CA1_6_9I1R6H.Encloses (homogeneousEntropy CA1_6_9I1R6Value) := by
  exact contains_sound (homogeneous_enclosed CA1_6_9I1R6Value CA1_6_9I1R6MassTerm_sound CA1_6_9I1R6Entropy_sound) (by decide +kernel)
lemma CA1_6_9I1ResidualEntropies_sound (k : Fin 17) :
    (CA1_6_9I1ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) k)) := by
  fin_cases k
  · exact CA1_6_9I1R0H_sound
  · exact CA1_6_9I1R1H_sound
  · exact CA1_6_9I1R2H_sound
  · exact CA1_6_9I1R3H_sound
  · exact CA1_6_9I1R4H_sound
  · exact CA1_6_9I1R5H_sound
  · exact CA1_6_9I1R6H_sound
  · exact CA1_6_9I1R7H_sound
  · exact CA1_6_9I1R8H_sound
  · exact CA1_6_9I1R9H_sound
  · exact CA1_6_9I1R10H_sound
  · exact CA1_6_9I1R11H_sound
  · exact CA1_6_9I1R12H_sound
  · exact CA1_6_9I1R13H_sound
  · exact CA1_6_9I1R14H_sound
  · exact CA1_6_9I1R15H_sound
  · exact CA1_6_9I1R16H_sound
lemma CA1_6_9I1Singles_sound (u : Shape) (hu : u ∈ below (shape 1 6 9))
    (hd : designated (Equiv.refl (Fin 3)) 1 u) :
    (CA1_6_9I1Singles u).Encloses (homogeneousEntropy ((fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) u)) := by
  rw [A1_6_9_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 0 8) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 1 7) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 2 6) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 3 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 4 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 5 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 6 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 0 7) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 1 6) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 2 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 3 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 4 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 5 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 6 1) by decide +kernel) hd |>.elim
lemma CA1_6_9I1Singleton_sound : CA1_6_9I1Singleton.Encloses
    (singletonEntropy (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 1 6 9)) A1_6_9Law (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1
    CA1_6_9I1Singles (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_6_9Law_sound u) CA1_6_9I1Singles_sound) (by decide +kernel)
lemma CA1_6_9I1Group_sound : CA1_6_9I1Group.Encloses
    (groupedEntropy (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CA1_6_9I1Singleton_sound
    (finSumBall_sound 17 CA1_6_9I1ResidualEntropies _ CA1_6_9I1ResidualEntropies_sound)) (by decide +kernel)

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
lemma CA1_6_9I1_sound_oai : CA1_6_9I1H.Encloses (stageACapacity (shape 1 6 9) 1) := by
  have hb := contains_sound (Ball.add_sound CA1_6_9I1PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CA1_6_9I1Group_sound)))
    (show contains (.add CA1_6_9I1PairH (.neg (.mul (.exact 2) CA1_6_9I1Group))) CA1_6_9I1H = true by decide +kernel)
  unfold CA1_6_9I1PairValue at hb
  simpa only [stageACapacity, nativeCapacity,
    show (1 : Fin 3) ≠ 0 by decide, ite_false, if_false, sub_eq_add_neg] using hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I1_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I1_sound_oai
