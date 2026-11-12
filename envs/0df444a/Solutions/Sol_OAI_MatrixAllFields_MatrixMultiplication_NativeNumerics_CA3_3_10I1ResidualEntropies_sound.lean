-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_3_10I1ResidualEntropies_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T14:05:23.819371+00:00
-- url     : https://prove2.me/submissions/4921535d-462d-4cbf-93db-190cb4d205d2

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
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_A3_3_10Law_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA3_3_10I1R10H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA3_3_10I1R11H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA3_3_10I1R12H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA3_3_10I1R13H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA3_3_10I1R14H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA3_3_10I1R15H_sound
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
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA3_3_10I1
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
lemma CA3_3_10I1R0Raw_sound (a : PairSlot) :
    (CA3_3_10I1R0Raw a).Encloses (CA3_3_10I1R0Value a) := by
  exact residualBall_sound_on (below (shape 3 3 10)) A3_3_10Law (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_3_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 3 10) (show (shape 3 3 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 0 a
lemma CA3_3_10I1R0Certificates_valid :
    CA3_3_10I1R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA3_3_10I1R0P_check : ∀ a : PairSlot, contains (CA3_3_10I1R0Raw a) (CA3_3_10I1R0P a) = true := by
  decide +kernel
lemma CA3_3_10I1R0P_sound (a : PairSlot) :
    (CA3_3_10I1R0P a).Encloses (CA3_3_10I1R0Value a) :=
  contains_sound (CA3_3_10I1R0Raw_sound a) (CA3_3_10I1R0P_check a)
lemma CA3_3_10I1R0Terms_sound (a : PairSlot) :
    (CA3_3_10I1R0Terms a).Encloses (Foundation.entropyTerm (CA3_3_10I1R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_3_10I1R0Certificates_valid
    (CA3_3_10I1R0CertificateIndex a) (CA3_3_10I1R0P_sound a)
lemma CA3_3_10I1R0Entropy_sound : CA3_3_10I1R0Entropy.Encloses (Foundation.finiteEntropy CA3_3_10I1R0Value) := by
  exact contains_sound (entropyPair_enclosed CA3_3_10I1R0Value CA3_3_10I1R0Terms CA3_3_10I1R0Terms_sound) (by decide +kernel)
lemma CA3_3_10I1R0Mass_sound : CA3_3_10I1R0Mass.Encloses (∑ a, CA3_3_10I1R0Value a) := by
  exact contains_sound (pairSumBall_sound CA3_3_10I1R0P CA3_3_10I1R0Value CA3_3_10I1R0P_sound) (by decide +kernel)
lemma CA3_3_10I1R0MassTermLog_sound : CA3_3_10I1R0MassTermLog.Encloses (Real.log ((∑ a, CA3_3_10I1R0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_3_10I1R0Mass_sound) (w := CA3_3_10I1R0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CA3_3_10I1R0MassTerm_sound : CA3_3_10I1R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_3_10I1R0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_3_10I1R0Mass_sound) CA3_3_10I1R0MassTermLog_sound) (by decide +kernel)
lemma CA3_3_10I1R0H_sound : CA3_3_10I1R0H.Encloses (homogeneousEntropy CA3_3_10I1R0Value) := by
  exact contains_sound (homogeneous_enclosed CA3_3_10I1R0Value CA3_3_10I1R0MassTerm_sound CA3_3_10I1R0Entropy_sound) (by decide +kernel)
lemma CA3_3_10I1R1Raw_sound (a : PairSlot) :
    (CA3_3_10I1R1Raw a).Encloses (CA3_3_10I1R1Value a) := by
  exact residualBall_sound_on (below (shape 3 3 10)) A3_3_10Law (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_3_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 3 10) (show (shape 3 3 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 1 a
lemma CA3_3_10I1R1Certificates_valid :
    CA3_3_10I1R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA3_3_10I1R1P_check : ∀ a : PairSlot, contains (CA3_3_10I1R1Raw a) (CA3_3_10I1R1P a) = true := by
  decide +kernel
lemma CA3_3_10I1R1P_sound (a : PairSlot) :
    (CA3_3_10I1R1P a).Encloses (CA3_3_10I1R1Value a) :=
  contains_sound (CA3_3_10I1R1Raw_sound a) (CA3_3_10I1R1P_check a)
lemma CA3_3_10I1R1Terms_sound (a : PairSlot) :
    (CA3_3_10I1R1Terms a).Encloses (Foundation.entropyTerm (CA3_3_10I1R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_3_10I1R1Certificates_valid
    (CA3_3_10I1R1CertificateIndex a) (CA3_3_10I1R1P_sound a)
lemma CA3_3_10I1R1Entropy_sound : CA3_3_10I1R1Entropy.Encloses (Foundation.finiteEntropy CA3_3_10I1R1Value) := by
  exact contains_sound (entropyPair_enclosed CA3_3_10I1R1Value CA3_3_10I1R1Terms CA3_3_10I1R1Terms_sound) (by decide +kernel)
lemma CA3_3_10I1R1Mass_sound : CA3_3_10I1R1Mass.Encloses (∑ a, CA3_3_10I1R1Value a) := by
  exact contains_sound (pairSumBall_sound CA3_3_10I1R1P CA3_3_10I1R1Value CA3_3_10I1R1P_sound) (by decide +kernel)
lemma CA3_3_10I1R1MassTermLog_sound : CA3_3_10I1R1MassTermLog.Encloses (Real.log ((∑ a, CA3_3_10I1R1Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_3_10I1R1Mass_sound) (w := CA3_3_10I1R1MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CA3_3_10I1R1MassTerm_sound : CA3_3_10I1R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_3_10I1R1Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_3_10I1R1Mass_sound) CA3_3_10I1R1MassTermLog_sound) (by decide +kernel)
lemma CA3_3_10I1R1H_sound : CA3_3_10I1R1H.Encloses (homogeneousEntropy CA3_3_10I1R1Value) := by
  exact contains_sound (homogeneous_enclosed CA3_3_10I1R1Value CA3_3_10I1R1MassTerm_sound CA3_3_10I1R1Entropy_sound) (by decide +kernel)
lemma CA3_3_10I1R2Raw_sound (a : PairSlot) :
    (CA3_3_10I1R2Raw a).Encloses (CA3_3_10I1R2Value a) := by
  exact residualBall_sound_on (below (shape 3 3 10)) A3_3_10Law (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_3_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 3 10) (show (shape 3 3 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 2 a
lemma CA3_3_10I1R2Certificates_valid :
    CA3_3_10I1R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA3_3_10I1R2P_check : ∀ a : PairSlot, contains (CA3_3_10I1R2Raw a) (CA3_3_10I1R2P a) = true := by
  decide +kernel
lemma CA3_3_10I1R2P_sound (a : PairSlot) :
    (CA3_3_10I1R2P a).Encloses (CA3_3_10I1R2Value a) :=
  contains_sound (CA3_3_10I1R2Raw_sound a) (CA3_3_10I1R2P_check a)
lemma CA3_3_10I1R2Terms_sound (a : PairSlot) :
    (CA3_3_10I1R2Terms a).Encloses (Foundation.entropyTerm (CA3_3_10I1R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_3_10I1R2Certificates_valid
    (CA3_3_10I1R2CertificateIndex a) (CA3_3_10I1R2P_sound a)
lemma CA3_3_10I1R2Entropy_sound : CA3_3_10I1R2Entropy.Encloses (Foundation.finiteEntropy CA3_3_10I1R2Value) := by
  exact contains_sound (entropyPair_enclosed CA3_3_10I1R2Value CA3_3_10I1R2Terms CA3_3_10I1R2Terms_sound) (by decide +kernel)
lemma CA3_3_10I1R2Mass_sound : CA3_3_10I1R2Mass.Encloses (∑ a, CA3_3_10I1R2Value a) := by
  exact contains_sound (pairSumBall_sound CA3_3_10I1R2P CA3_3_10I1R2Value CA3_3_10I1R2P_sound) (by decide +kernel)
lemma CA3_3_10I1R2MassTermLog_sound : CA3_3_10I1R2MassTermLog.Encloses (Real.log ((∑ a, CA3_3_10I1R2Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_3_10I1R2Mass_sound) (w := CA3_3_10I1R2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CA3_3_10I1R2MassTerm_sound : CA3_3_10I1R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_3_10I1R2Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_3_10I1R2Mass_sound) CA3_3_10I1R2MassTermLog_sound) (by decide +kernel)
lemma CA3_3_10I1R2H_sound : CA3_3_10I1R2H.Encloses (homogeneousEntropy CA3_3_10I1R2Value) := by
  exact contains_sound (homogeneous_enclosed CA3_3_10I1R2Value CA3_3_10I1R2MassTerm_sound CA3_3_10I1R2Entropy_sound) (by decide +kernel)
lemma CA3_3_10I1R3Raw_sound (a : PairSlot) :
    (CA3_3_10I1R3Raw a).Encloses (CA3_3_10I1R3Value a) := by
  exact residualBall_sound_on (below (shape 3 3 10)) A3_3_10Law (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_3_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 3 10) (show (shape 3 3 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 3 a
lemma CA3_3_10I1R3Certificates_valid :
    CA3_3_10I1R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA3_3_10I1R3P_check : ∀ a : PairSlot, contains (CA3_3_10I1R3Raw a) (CA3_3_10I1R3P a) = true := by
  decide +kernel
lemma CA3_3_10I1R3P_sound (a : PairSlot) :
    (CA3_3_10I1R3P a).Encloses (CA3_3_10I1R3Value a) :=
  contains_sound (CA3_3_10I1R3Raw_sound a) (CA3_3_10I1R3P_check a)
lemma CA3_3_10I1R3Terms_sound (a : PairSlot) :
    (CA3_3_10I1R3Terms a).Encloses (Foundation.entropyTerm (CA3_3_10I1R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_3_10I1R3Certificates_valid
    (CA3_3_10I1R3CertificateIndex a) (CA3_3_10I1R3P_sound a)
lemma CA3_3_10I1R3Entropy_sound : CA3_3_10I1R3Entropy.Encloses (Foundation.finiteEntropy CA3_3_10I1R3Value) := by
  exact contains_sound (entropyPair_enclosed CA3_3_10I1R3Value CA3_3_10I1R3Terms CA3_3_10I1R3Terms_sound) (by decide +kernel)
lemma CA3_3_10I1R3Mass_sound : CA3_3_10I1R3Mass.Encloses (∑ a, CA3_3_10I1R3Value a) := by
  exact contains_sound (pairSumBall_sound CA3_3_10I1R3P CA3_3_10I1R3Value CA3_3_10I1R3P_sound) (by decide +kernel)
lemma CA3_3_10I1R3MassTermLog_sound : CA3_3_10I1R3MassTermLog.Encloses (Real.log ((∑ a, CA3_3_10I1R3Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_3_10I1R3Mass_sound) (w := CA3_3_10I1R3MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CA3_3_10I1R3MassTerm_sound : CA3_3_10I1R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_3_10I1R3Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_3_10I1R3Mass_sound) CA3_3_10I1R3MassTermLog_sound) (by decide +kernel)
lemma CA3_3_10I1R3H_sound : CA3_3_10I1R3H.Encloses (homogeneousEntropy CA3_3_10I1R3Value) := by
  exact contains_sound (homogeneous_enclosed CA3_3_10I1R3Value CA3_3_10I1R3MassTerm_sound CA3_3_10I1R3Entropy_sound) (by decide +kernel)
lemma CA3_3_10I1R4Raw_sound (a : PairSlot) :
    (CA3_3_10I1R4Raw a).Encloses (CA3_3_10I1R4Value a) := by
  exact residualBall_sound_on (below (shape 3 3 10)) A3_3_10Law (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_3_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 3 10) (show (shape 3 3 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 4 a
lemma CA3_3_10I1R4Certificates_valid :
    CA3_3_10I1R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA3_3_10I1R4P_check : ∀ a : PairSlot, contains (CA3_3_10I1R4Raw a) (CA3_3_10I1R4P a) = true := by
  decide +kernel
lemma CA3_3_10I1R4P_sound (a : PairSlot) :
    (CA3_3_10I1R4P a).Encloses (CA3_3_10I1R4Value a) :=
  contains_sound (CA3_3_10I1R4Raw_sound a) (CA3_3_10I1R4P_check a)
lemma CA3_3_10I1R4Terms_sound (a : PairSlot) :
    (CA3_3_10I1R4Terms a).Encloses (Foundation.entropyTerm (CA3_3_10I1R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_3_10I1R4Certificates_valid
    (CA3_3_10I1R4CertificateIndex a) (CA3_3_10I1R4P_sound a)
lemma CA3_3_10I1R4Entropy_sound : CA3_3_10I1R4Entropy.Encloses (Foundation.finiteEntropy CA3_3_10I1R4Value) := by
  exact contains_sound (entropyPair_enclosed CA3_3_10I1R4Value CA3_3_10I1R4Terms CA3_3_10I1R4Terms_sound) (by decide +kernel)
lemma CA3_3_10I1R4Mass_sound : CA3_3_10I1R4Mass.Encloses (∑ a, CA3_3_10I1R4Value a) := by
  exact contains_sound (pairSumBall_sound CA3_3_10I1R4P CA3_3_10I1R4Value CA3_3_10I1R4P_sound) (by decide +kernel)
lemma CA3_3_10I1R4MassTerm_sound : CA3_3_10I1R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_3_10I1R4Value a))) :=
  entropyTerm_zero_ball (CA3_3_10I1R4Mass_sound)
lemma CA3_3_10I1R4H_sound : CA3_3_10I1R4H.Encloses (homogeneousEntropy CA3_3_10I1R4Value) := by
  exact contains_sound (homogeneous_enclosed CA3_3_10I1R4Value CA3_3_10I1R4MassTerm_sound CA3_3_10I1R4Entropy_sound) (by decide +kernel)
lemma CA3_3_10I1R5Raw_sound (a : PairSlot) :
    (CA3_3_10I1R5Raw a).Encloses (CA3_3_10I1R5Value a) := by
  exact residualBall_sound_on (below (shape 3 3 10)) A3_3_10Law (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_3_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 3 10) (show (shape 3 3 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 5 a
lemma CA3_3_10I1R5Certificates_valid :
    CA3_3_10I1R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA3_3_10I1R5P_check : ∀ a : PairSlot, contains (CA3_3_10I1R5Raw a) (CA3_3_10I1R5P a) = true := by
  decide +kernel
lemma CA3_3_10I1R5P_sound (a : PairSlot) :
    (CA3_3_10I1R5P a).Encloses (CA3_3_10I1R5Value a) :=
  contains_sound (CA3_3_10I1R5Raw_sound a) (CA3_3_10I1R5P_check a)
lemma CA3_3_10I1R5Terms_sound (a : PairSlot) :
    (CA3_3_10I1R5Terms a).Encloses (Foundation.entropyTerm (CA3_3_10I1R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_3_10I1R5Certificates_valid
    (CA3_3_10I1R5CertificateIndex a) (CA3_3_10I1R5P_sound a)
lemma CA3_3_10I1R5Entropy_sound : CA3_3_10I1R5Entropy.Encloses (Foundation.finiteEntropy CA3_3_10I1R5Value) := by
  exact contains_sound (entropyPair_enclosed CA3_3_10I1R5Value CA3_3_10I1R5Terms CA3_3_10I1R5Terms_sound) (by decide +kernel)
lemma CA3_3_10I1R5Mass_sound : CA3_3_10I1R5Mass.Encloses (∑ a, CA3_3_10I1R5Value a) := by
  exact contains_sound (pairSumBall_sound CA3_3_10I1R5P CA3_3_10I1R5Value CA3_3_10I1R5P_sound) (by decide +kernel)
lemma CA3_3_10I1R5MassTerm_sound : CA3_3_10I1R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_3_10I1R5Value a))) :=
  entropyTerm_zero_ball (CA3_3_10I1R5Mass_sound)
lemma CA3_3_10I1R5H_sound : CA3_3_10I1R5H.Encloses (homogeneousEntropy CA3_3_10I1R5Value) := by
  exact contains_sound (homogeneous_enclosed CA3_3_10I1R5Value CA3_3_10I1R5MassTerm_sound CA3_3_10I1R5Entropy_sound) (by decide +kernel)
lemma CA3_3_10I1R6Raw_sound (a : PairSlot) :
    (CA3_3_10I1R6Raw a).Encloses (CA3_3_10I1R6Value a) := by
  exact residualBall_sound_on (below (shape 3 3 10)) A3_3_10Law (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_3_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 3 10) (show (shape 3 3 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 6 a
lemma CA3_3_10I1R6Certificates_valid :
    CA3_3_10I1R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA3_3_10I1R6P_check : ∀ a : PairSlot, contains (CA3_3_10I1R6Raw a) (CA3_3_10I1R6P a) = true := by
  decide +kernel
lemma CA3_3_10I1R6P_sound (a : PairSlot) :
    (CA3_3_10I1R6P a).Encloses (CA3_3_10I1R6Value a) :=
  contains_sound (CA3_3_10I1R6Raw_sound a) (CA3_3_10I1R6P_check a)
lemma CA3_3_10I1R6Terms_sound (a : PairSlot) :
    (CA3_3_10I1R6Terms a).Encloses (Foundation.entropyTerm (CA3_3_10I1R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_3_10I1R6Certificates_valid
    (CA3_3_10I1R6CertificateIndex a) (CA3_3_10I1R6P_sound a)
lemma CA3_3_10I1R6Entropy_sound : CA3_3_10I1R6Entropy.Encloses (Foundation.finiteEntropy CA3_3_10I1R6Value) := by
  exact contains_sound (entropyPair_enclosed CA3_3_10I1R6Value CA3_3_10I1R6Terms CA3_3_10I1R6Terms_sound) (by decide +kernel)
lemma CA3_3_10I1R6Mass_sound : CA3_3_10I1R6Mass.Encloses (∑ a, CA3_3_10I1R6Value a) := by
  exact contains_sound (pairSumBall_sound CA3_3_10I1R6P CA3_3_10I1R6Value CA3_3_10I1R6P_sound) (by decide +kernel)
lemma CA3_3_10I1R6MassTerm_sound : CA3_3_10I1R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_3_10I1R6Value a))) :=
  entropyTerm_zero_ball (CA3_3_10I1R6Mass_sound)
lemma CA3_3_10I1R6H_sound : CA3_3_10I1R6H.Encloses (homogeneousEntropy CA3_3_10I1R6Value) := by
  exact contains_sound (homogeneous_enclosed CA3_3_10I1R6Value CA3_3_10I1R6MassTerm_sound CA3_3_10I1R6Entropy_sound) (by decide +kernel)
lemma CA3_3_10I1R7Raw_sound (a : PairSlot) :
    (CA3_3_10I1R7Raw a).Encloses (CA3_3_10I1R7Value a) := by
  exact residualBall_sound_on (below (shape 3 3 10)) A3_3_10Law (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_3_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 3 10) (show (shape 3 3 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 7 a
lemma CA3_3_10I1R7Certificates_valid :
    CA3_3_10I1R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA3_3_10I1R7P_check : ∀ a : PairSlot, contains (CA3_3_10I1R7Raw a) (CA3_3_10I1R7P a) = true := by
  decide +kernel
lemma CA3_3_10I1R7P_sound (a : PairSlot) :
    (CA3_3_10I1R7P a).Encloses (CA3_3_10I1R7Value a) :=
  contains_sound (CA3_3_10I1R7Raw_sound a) (CA3_3_10I1R7P_check a)
lemma CA3_3_10I1R7Terms_sound (a : PairSlot) :
    (CA3_3_10I1R7Terms a).Encloses (Foundation.entropyTerm (CA3_3_10I1R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_3_10I1R7Certificates_valid
    (CA3_3_10I1R7CertificateIndex a) (CA3_3_10I1R7P_sound a)
lemma CA3_3_10I1R7Entropy_sound : CA3_3_10I1R7Entropy.Encloses (Foundation.finiteEntropy CA3_3_10I1R7Value) := by
  exact contains_sound (entropyPair_enclosed CA3_3_10I1R7Value CA3_3_10I1R7Terms CA3_3_10I1R7Terms_sound) (by decide +kernel)
lemma CA3_3_10I1R7Mass_sound : CA3_3_10I1R7Mass.Encloses (∑ a, CA3_3_10I1R7Value a) := by
  exact contains_sound (pairSumBall_sound CA3_3_10I1R7P CA3_3_10I1R7Value CA3_3_10I1R7P_sound) (by decide +kernel)
lemma CA3_3_10I1R7MassTerm_sound : CA3_3_10I1R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_3_10I1R7Value a))) :=
  entropyTerm_zero_ball (CA3_3_10I1R7Mass_sound)
lemma CA3_3_10I1R7H_sound : CA3_3_10I1R7H.Encloses (homogeneousEntropy CA3_3_10I1R7Value) := by
  exact contains_sound (homogeneous_enclosed CA3_3_10I1R7Value CA3_3_10I1R7MassTerm_sound CA3_3_10I1R7Entropy_sound) (by decide +kernel)
lemma CA3_3_10I1R8Raw_sound (a : PairSlot) :
    (CA3_3_10I1R8Raw a).Encloses (CA3_3_10I1R8Value a) := by
  exact residualBall_sound_on (below (shape 3 3 10)) A3_3_10Law (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_3_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 3 10) (show (shape 3 3 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 8 a
lemma CA3_3_10I1R8Certificates_valid :
    CA3_3_10I1R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA3_3_10I1R8P_check : ∀ a : PairSlot, contains (CA3_3_10I1R8Raw a) (CA3_3_10I1R8P a) = true := by
  decide +kernel
lemma CA3_3_10I1R8P_sound (a : PairSlot) :
    (CA3_3_10I1R8P a).Encloses (CA3_3_10I1R8Value a) :=
  contains_sound (CA3_3_10I1R8Raw_sound a) (CA3_3_10I1R8P_check a)
lemma CA3_3_10I1R8Terms_sound (a : PairSlot) :
    (CA3_3_10I1R8Terms a).Encloses (Foundation.entropyTerm (CA3_3_10I1R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_3_10I1R8Certificates_valid
    (CA3_3_10I1R8CertificateIndex a) (CA3_3_10I1R8P_sound a)
lemma CA3_3_10I1R8Entropy_sound : CA3_3_10I1R8Entropy.Encloses (Foundation.finiteEntropy CA3_3_10I1R8Value) := by
  exact contains_sound (entropyPair_enclosed CA3_3_10I1R8Value CA3_3_10I1R8Terms CA3_3_10I1R8Terms_sound) (by decide +kernel)
lemma CA3_3_10I1R8Mass_sound : CA3_3_10I1R8Mass.Encloses (∑ a, CA3_3_10I1R8Value a) := by
  exact contains_sound (pairSumBall_sound CA3_3_10I1R8P CA3_3_10I1R8Value CA3_3_10I1R8P_sound) (by decide +kernel)
lemma CA3_3_10I1R8MassTerm_sound : CA3_3_10I1R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_3_10I1R8Value a))) :=
  entropyTerm_zero_ball (CA3_3_10I1R8Mass_sound)
lemma CA3_3_10I1R8H_sound : CA3_3_10I1R8H.Encloses (homogeneousEntropy CA3_3_10I1R8Value) := by
  exact contains_sound (homogeneous_enclosed CA3_3_10I1R8Value CA3_3_10I1R8MassTerm_sound CA3_3_10I1R8Entropy_sound) (by decide +kernel)
lemma CA3_3_10I1R9Raw_sound (a : PairSlot) :
    (CA3_3_10I1R9Raw a).Encloses (CA3_3_10I1R9Value a) := by
  exact residualBall_sound_on (below (shape 3 3 10)) A3_3_10Law (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_3_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 3 10) (show (shape 3 3 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 9 a
lemma CA3_3_10I1R9Certificates_valid :
    CA3_3_10I1R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA3_3_10I1R9P_check : ∀ a : PairSlot, contains (CA3_3_10I1R9Raw a) (CA3_3_10I1R9P a) = true := by
  decide +kernel
lemma CA3_3_10I1R9P_sound (a : PairSlot) :
    (CA3_3_10I1R9P a).Encloses (CA3_3_10I1R9Value a) :=
  contains_sound (CA3_3_10I1R9Raw_sound a) (CA3_3_10I1R9P_check a)
lemma CA3_3_10I1R9Terms_sound (a : PairSlot) :
    (CA3_3_10I1R9Terms a).Encloses (Foundation.entropyTerm (CA3_3_10I1R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_3_10I1R9Certificates_valid
    (CA3_3_10I1R9CertificateIndex a) (CA3_3_10I1R9P_sound a)
lemma CA3_3_10I1R9Entropy_sound : CA3_3_10I1R9Entropy.Encloses (Foundation.finiteEntropy CA3_3_10I1R9Value) := by
  exact contains_sound (entropyPair_enclosed CA3_3_10I1R9Value CA3_3_10I1R9Terms CA3_3_10I1R9Terms_sound) (by decide +kernel)
lemma CA3_3_10I1R9Mass_sound : CA3_3_10I1R9Mass.Encloses (∑ a, CA3_3_10I1R9Value a) := by
  exact contains_sound (pairSumBall_sound CA3_3_10I1R9P CA3_3_10I1R9Value CA3_3_10I1R9P_sound) (by decide +kernel)
lemma CA3_3_10I1R9MassTerm_sound : CA3_3_10I1R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_3_10I1R9Value a))) :=
  entropyTerm_zero_ball (CA3_3_10I1R9Mass_sound)
lemma CA3_3_10I1R9H_sound : CA3_3_10I1R9H.Encloses (homogeneousEntropy CA3_3_10I1R9Value) := by
  exact contains_sound (homogeneous_enclosed CA3_3_10I1R9Value CA3_3_10I1R9MassTerm_sound CA3_3_10I1R9Entropy_sound) (by decide +kernel)
lemma CA3_3_10I1R16Raw_sound (a : PairSlot) :
    (CA3_3_10I1R16Raw a).Encloses (CA3_3_10I1R16Value a) := by
  exact residualBall_sound_on (below (shape 3 3 10)) A3_3_10Law (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_3_10Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 3 10) (show (shape 3 3 10) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 16 a
lemma CA3_3_10I1R16Certificates_valid :
    CA3_3_10I1R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA3_3_10I1R16P_check : ∀ a : PairSlot, contains (CA3_3_10I1R16Raw a) (CA3_3_10I1R16P a) = true := by
  decide +kernel
lemma CA3_3_10I1R16P_sound (a : PairSlot) :
    (CA3_3_10I1R16P a).Encloses (CA3_3_10I1R16Value a) :=
  contains_sound (CA3_3_10I1R16Raw_sound a) (CA3_3_10I1R16P_check a)
lemma CA3_3_10I1R16Terms_sound (a : PairSlot) :
    (CA3_3_10I1R16Terms a).Encloses (Foundation.entropyTerm (CA3_3_10I1R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_3_10I1R16Certificates_valid
    (CA3_3_10I1R16CertificateIndex a) (CA3_3_10I1R16P_sound a)
lemma CA3_3_10I1R16Entropy_sound : CA3_3_10I1R16Entropy.Encloses (Foundation.finiteEntropy CA3_3_10I1R16Value) := by
  exact contains_sound (entropyPair_enclosed CA3_3_10I1R16Value CA3_3_10I1R16Terms CA3_3_10I1R16Terms_sound) (by decide +kernel)
lemma CA3_3_10I1R16Mass_sound : CA3_3_10I1R16Mass.Encloses (∑ a, CA3_3_10I1R16Value a) := by
  exact contains_sound (pairSumBall_sound CA3_3_10I1R16P CA3_3_10I1R16Value CA3_3_10I1R16P_sound) (by decide +kernel)
lemma CA3_3_10I1R16MassTerm_sound : CA3_3_10I1R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_3_10I1R16Value a))) :=
  entropyTerm_zero_ball (CA3_3_10I1R16Mass_sound)
lemma CA3_3_10I1R16H_sound : CA3_3_10I1R16H.Encloses (homogeneousEntropy CA3_3_10I1R16Value) := by
  exact contains_sound (homogeneous_enclosed CA3_3_10I1R16Value CA3_3_10I1R16MassTerm_sound CA3_3_10I1R16Entropy_sound) (by decide +kernel)
lemma CA3_3_10I1ResidualEntropies_sound_oai (k : Fin 17) :
    (CA3_3_10I1ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 3 3 10)) (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) k)) := by
  fin_cases k
  · exact CA3_3_10I1R0H_sound
  · exact CA3_3_10I1R1H_sound
  · exact CA3_3_10I1R2H_sound
  · exact CA3_3_10I1R3H_sound
  · exact CA3_3_10I1R4H_sound
  · exact CA3_3_10I1R5H_sound
  · exact CA3_3_10I1R6H_sound
  · exact CA3_3_10I1R7H_sound
  · exact CA3_3_10I1R8H_sound
  · exact CA3_3_10I1R9H_sound
  · exact CA3_3_10I1R10H_sound
  · exact CA3_3_10I1R11H_sound
  · exact CA3_3_10I1R12H_sound
  · exact CA3_3_10I1R13H_sound
  · exact CA3_3_10I1R14H_sound
  · exact CA3_3_10I1R15H_sound
  · exact CA3_3_10I1R16H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_3_10I1ResidualEntropies_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_3_10I1ResidualEntropies_sound_oai
