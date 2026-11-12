-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_7_7I1Group_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T14:03:37.07495+00:00
-- url     : https://prove2.me/submissions/45a4b311-4482-4add-b7c4-31fc886df747

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
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_A2_7_7Law_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA2_7_7I1Singleton_sound
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
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA2_7_7I1
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
lemma CA2_7_7I1R0Raw_sound (a : PairSlot) :
    (CA2_7_7I1R0Raw a).Encloses (CA2_7_7I1R0Value a) := by
  exact residualBall_sound_on (below (shape 2 7 7)) A2_7_7Law (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_7_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 7 7) (show (shape 2 7 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 0 a
lemma CA2_7_7I1R0Certificates_valid :
    CA2_7_7I1R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA2_7_7I1R0P_check : ∀ a : PairSlot, contains (CA2_7_7I1R0Raw a) (CA2_7_7I1R0P a) = true := by
  decide +kernel
lemma CA2_7_7I1R0P_sound (a : PairSlot) :
    (CA2_7_7I1R0P a).Encloses (CA2_7_7I1R0Value a) :=
  contains_sound (CA2_7_7I1R0Raw_sound a) (CA2_7_7I1R0P_check a)
lemma CA2_7_7I1R0Terms_sound (a : PairSlot) :
    (CA2_7_7I1R0Terms a).Encloses (Foundation.entropyTerm (CA2_7_7I1R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_7_7I1R0Certificates_valid
    (CA2_7_7I1R0CertificateIndex a) (CA2_7_7I1R0P_sound a)
lemma CA2_7_7I1R0Entropy_sound : CA2_7_7I1R0Entropy.Encloses (Foundation.finiteEntropy CA2_7_7I1R0Value) := by
  exact contains_sound (entropyPair_enclosed CA2_7_7I1R0Value CA2_7_7I1R0Terms CA2_7_7I1R0Terms_sound) (by decide +kernel)
lemma CA2_7_7I1R0Mass_sound : CA2_7_7I1R0Mass.Encloses (∑ a, CA2_7_7I1R0Value a) := by
  exact contains_sound (pairSumBall_sound CA2_7_7I1R0P CA2_7_7I1R0Value CA2_7_7I1R0P_sound) (by decide +kernel)
lemma CA2_7_7I1R0MassTermLog_sound : CA2_7_7I1R0MassTermLog.Encloses (Real.log ((∑ a, CA2_7_7I1R0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_7_7I1R0Mass_sound) (w := CA2_7_7I1R0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CA2_7_7I1R0MassTerm_sound : CA2_7_7I1R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_7_7I1R0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_7_7I1R0Mass_sound) CA2_7_7I1R0MassTermLog_sound) (by decide +kernel)
lemma CA2_7_7I1R0H_sound : CA2_7_7I1R0H.Encloses (homogeneousEntropy CA2_7_7I1R0Value) := by
  exact contains_sound (homogeneous_enclosed CA2_7_7I1R0Value CA2_7_7I1R0MassTerm_sound CA2_7_7I1R0Entropy_sound) (by decide +kernel)
lemma CA2_7_7I1R1Raw_sound (a : PairSlot) :
    (CA2_7_7I1R1Raw a).Encloses (CA2_7_7I1R1Value a) := by
  exact residualBall_sound_on (below (shape 2 7 7)) A2_7_7Law (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_7_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 7 7) (show (shape 2 7 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 1 a
lemma CA2_7_7I1R1Certificates_valid :
    CA2_7_7I1R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA2_7_7I1R1P_check : ∀ a : PairSlot, contains (CA2_7_7I1R1Raw a) (CA2_7_7I1R1P a) = true := by
  decide +kernel
lemma CA2_7_7I1R1P_sound (a : PairSlot) :
    (CA2_7_7I1R1P a).Encloses (CA2_7_7I1R1Value a) :=
  contains_sound (CA2_7_7I1R1Raw_sound a) (CA2_7_7I1R1P_check a)
lemma CA2_7_7I1R1Terms_sound (a : PairSlot) :
    (CA2_7_7I1R1Terms a).Encloses (Foundation.entropyTerm (CA2_7_7I1R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_7_7I1R1Certificates_valid
    (CA2_7_7I1R1CertificateIndex a) (CA2_7_7I1R1P_sound a)
lemma CA2_7_7I1R1Entropy_sound : CA2_7_7I1R1Entropy.Encloses (Foundation.finiteEntropy CA2_7_7I1R1Value) := by
  exact contains_sound (entropyPair_enclosed CA2_7_7I1R1Value CA2_7_7I1R1Terms CA2_7_7I1R1Terms_sound) (by decide +kernel)
lemma CA2_7_7I1R1Mass_sound : CA2_7_7I1R1Mass.Encloses (∑ a, CA2_7_7I1R1Value a) := by
  exact contains_sound (pairSumBall_sound CA2_7_7I1R1P CA2_7_7I1R1Value CA2_7_7I1R1P_sound) (by decide +kernel)
lemma CA2_7_7I1R1MassTermLog_sound : CA2_7_7I1R1MassTermLog.Encloses (Real.log ((∑ a, CA2_7_7I1R1Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_7_7I1R1Mass_sound) (w := CA2_7_7I1R1MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CA2_7_7I1R1MassTerm_sound : CA2_7_7I1R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_7_7I1R1Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_7_7I1R1Mass_sound) CA2_7_7I1R1MassTermLog_sound) (by decide +kernel)
lemma CA2_7_7I1R1H_sound : CA2_7_7I1R1H.Encloses (homogeneousEntropy CA2_7_7I1R1Value) := by
  exact contains_sound (homogeneous_enclosed CA2_7_7I1R1Value CA2_7_7I1R1MassTerm_sound CA2_7_7I1R1Entropy_sound) (by decide +kernel)
lemma CA2_7_7I1R2Raw_sound (a : PairSlot) :
    (CA2_7_7I1R2Raw a).Encloses (CA2_7_7I1R2Value a) := by
  exact residualBall_sound_on (below (shape 2 7 7)) A2_7_7Law (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_7_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 7 7) (show (shape 2 7 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 2 a
lemma CA2_7_7I1R2Certificates_valid :
    CA2_7_7I1R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA2_7_7I1R2P_check : ∀ a : PairSlot, contains (CA2_7_7I1R2Raw a) (CA2_7_7I1R2P a) = true := by
  decide +kernel
lemma CA2_7_7I1R2P_sound (a : PairSlot) :
    (CA2_7_7I1R2P a).Encloses (CA2_7_7I1R2Value a) :=
  contains_sound (CA2_7_7I1R2Raw_sound a) (CA2_7_7I1R2P_check a)
lemma CA2_7_7I1R2Terms_sound (a : PairSlot) :
    (CA2_7_7I1R2Terms a).Encloses (Foundation.entropyTerm (CA2_7_7I1R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_7_7I1R2Certificates_valid
    (CA2_7_7I1R2CertificateIndex a) (CA2_7_7I1R2P_sound a)
lemma CA2_7_7I1R2Entropy_sound : CA2_7_7I1R2Entropy.Encloses (Foundation.finiteEntropy CA2_7_7I1R2Value) := by
  exact contains_sound (entropyPair_enclosed CA2_7_7I1R2Value CA2_7_7I1R2Terms CA2_7_7I1R2Terms_sound) (by decide +kernel)
lemma CA2_7_7I1R2Mass_sound : CA2_7_7I1R2Mass.Encloses (∑ a, CA2_7_7I1R2Value a) := by
  exact contains_sound (pairSumBall_sound CA2_7_7I1R2P CA2_7_7I1R2Value CA2_7_7I1R2P_sound) (by decide +kernel)
lemma CA2_7_7I1R2MassTermLog_sound : CA2_7_7I1R2MassTermLog.Encloses (Real.log ((∑ a, CA2_7_7I1R2Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_7_7I1R2Mass_sound) (w := CA2_7_7I1R2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CA2_7_7I1R2MassTerm_sound : CA2_7_7I1R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_7_7I1R2Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_7_7I1R2Mass_sound) CA2_7_7I1R2MassTermLog_sound) (by decide +kernel)
lemma CA2_7_7I1R2H_sound : CA2_7_7I1R2H.Encloses (homogeneousEntropy CA2_7_7I1R2Value) := by
  exact contains_sound (homogeneous_enclosed CA2_7_7I1R2Value CA2_7_7I1R2MassTerm_sound CA2_7_7I1R2Entropy_sound) (by decide +kernel)
lemma CA2_7_7I1R3Raw_sound (a : PairSlot) :
    (CA2_7_7I1R3Raw a).Encloses (CA2_7_7I1R3Value a) := by
  exact residualBall_sound_on (below (shape 2 7 7)) A2_7_7Law (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_7_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 7 7) (show (shape 2 7 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 3 a
lemma CA2_7_7I1R3Certificates_valid :
    CA2_7_7I1R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA2_7_7I1R3P_check : ∀ a : PairSlot, contains (CA2_7_7I1R3Raw a) (CA2_7_7I1R3P a) = true := by
  decide +kernel
lemma CA2_7_7I1R3P_sound (a : PairSlot) :
    (CA2_7_7I1R3P a).Encloses (CA2_7_7I1R3Value a) :=
  contains_sound (CA2_7_7I1R3Raw_sound a) (CA2_7_7I1R3P_check a)
lemma CA2_7_7I1R3Terms_sound (a : PairSlot) :
    (CA2_7_7I1R3Terms a).Encloses (Foundation.entropyTerm (CA2_7_7I1R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_7_7I1R3Certificates_valid
    (CA2_7_7I1R3CertificateIndex a) (CA2_7_7I1R3P_sound a)
lemma CA2_7_7I1R3Entropy_sound : CA2_7_7I1R3Entropy.Encloses (Foundation.finiteEntropy CA2_7_7I1R3Value) := by
  exact contains_sound (entropyPair_enclosed CA2_7_7I1R3Value CA2_7_7I1R3Terms CA2_7_7I1R3Terms_sound) (by decide +kernel)
lemma CA2_7_7I1R3Mass_sound : CA2_7_7I1R3Mass.Encloses (∑ a, CA2_7_7I1R3Value a) := by
  exact contains_sound (pairSumBall_sound CA2_7_7I1R3P CA2_7_7I1R3Value CA2_7_7I1R3P_sound) (by decide +kernel)
lemma CA2_7_7I1R3MassTermLog_sound : CA2_7_7I1R3MassTermLog.Encloses (Real.log ((∑ a, CA2_7_7I1R3Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_7_7I1R3Mass_sound) (w := CA2_7_7I1R3MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CA2_7_7I1R3MassTerm_sound : CA2_7_7I1R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_7_7I1R3Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_7_7I1R3Mass_sound) CA2_7_7I1R3MassTermLog_sound) (by decide +kernel)
lemma CA2_7_7I1R3H_sound : CA2_7_7I1R3H.Encloses (homogeneousEntropy CA2_7_7I1R3Value) := by
  exact contains_sound (homogeneous_enclosed CA2_7_7I1R3Value CA2_7_7I1R3MassTerm_sound CA2_7_7I1R3Entropy_sound) (by decide +kernel)
lemma CA2_7_7I1R4Raw_sound (a : PairSlot) :
    (CA2_7_7I1R4Raw a).Encloses (CA2_7_7I1R4Value a) := by
  exact residualBall_sound_on (below (shape 2 7 7)) A2_7_7Law (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_7_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 7 7) (show (shape 2 7 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 4 a
lemma CA2_7_7I1R4Certificates_valid :
    CA2_7_7I1R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA2_7_7I1R4P_check : ∀ a : PairSlot, contains (CA2_7_7I1R4Raw a) (CA2_7_7I1R4P a) = true := by
  decide +kernel
lemma CA2_7_7I1R4P_sound (a : PairSlot) :
    (CA2_7_7I1R4P a).Encloses (CA2_7_7I1R4Value a) :=
  contains_sound (CA2_7_7I1R4Raw_sound a) (CA2_7_7I1R4P_check a)
lemma CA2_7_7I1R4Terms_sound (a : PairSlot) :
    (CA2_7_7I1R4Terms a).Encloses (Foundation.entropyTerm (CA2_7_7I1R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_7_7I1R4Certificates_valid
    (CA2_7_7I1R4CertificateIndex a) (CA2_7_7I1R4P_sound a)
lemma CA2_7_7I1R4Entropy_sound : CA2_7_7I1R4Entropy.Encloses (Foundation.finiteEntropy CA2_7_7I1R4Value) := by
  exact contains_sound (entropyPair_enclosed CA2_7_7I1R4Value CA2_7_7I1R4Terms CA2_7_7I1R4Terms_sound) (by decide +kernel)
lemma CA2_7_7I1R4Mass_sound : CA2_7_7I1R4Mass.Encloses (∑ a, CA2_7_7I1R4Value a) := by
  exact contains_sound (pairSumBall_sound CA2_7_7I1R4P CA2_7_7I1R4Value CA2_7_7I1R4P_sound) (by decide +kernel)
lemma CA2_7_7I1R4MassTermLog_sound : CA2_7_7I1R4MassTermLog.Encloses (Real.log ((∑ a, CA2_7_7I1R4Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_7_7I1R4Mass_sound) (w := CA2_7_7I1R4MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CA2_7_7I1R4MassTerm_sound : CA2_7_7I1R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_7_7I1R4Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_7_7I1R4Mass_sound) CA2_7_7I1R4MassTermLog_sound) (by decide +kernel)
lemma CA2_7_7I1R4H_sound : CA2_7_7I1R4H.Encloses (homogeneousEntropy CA2_7_7I1R4Value) := by
  exact contains_sound (homogeneous_enclosed CA2_7_7I1R4Value CA2_7_7I1R4MassTerm_sound CA2_7_7I1R4Entropy_sound) (by decide +kernel)
lemma CA2_7_7I1R5Raw_sound (a : PairSlot) :
    (CA2_7_7I1R5Raw a).Encloses (CA2_7_7I1R5Value a) := by
  exact residualBall_sound_on (below (shape 2 7 7)) A2_7_7Law (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_7_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 7 7) (show (shape 2 7 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 5 a
lemma CA2_7_7I1R5Certificates_valid :
    CA2_7_7I1R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA2_7_7I1R5P_check : ∀ a : PairSlot, contains (CA2_7_7I1R5Raw a) (CA2_7_7I1R5P a) = true := by
  decide +kernel
lemma CA2_7_7I1R5P_sound (a : PairSlot) :
    (CA2_7_7I1R5P a).Encloses (CA2_7_7I1R5Value a) :=
  contains_sound (CA2_7_7I1R5Raw_sound a) (CA2_7_7I1R5P_check a)
lemma CA2_7_7I1R5Terms_sound (a : PairSlot) :
    (CA2_7_7I1R5Terms a).Encloses (Foundation.entropyTerm (CA2_7_7I1R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_7_7I1R5Certificates_valid
    (CA2_7_7I1R5CertificateIndex a) (CA2_7_7I1R5P_sound a)
lemma CA2_7_7I1R5Entropy_sound : CA2_7_7I1R5Entropy.Encloses (Foundation.finiteEntropy CA2_7_7I1R5Value) := by
  exact contains_sound (entropyPair_enclosed CA2_7_7I1R5Value CA2_7_7I1R5Terms CA2_7_7I1R5Terms_sound) (by decide +kernel)
lemma CA2_7_7I1R5Mass_sound : CA2_7_7I1R5Mass.Encloses (∑ a, CA2_7_7I1R5Value a) := by
  exact contains_sound (pairSumBall_sound CA2_7_7I1R5P CA2_7_7I1R5Value CA2_7_7I1R5P_sound) (by decide +kernel)
lemma CA2_7_7I1R5MassTermLog_sound : CA2_7_7I1R5MassTermLog.Encloses (Real.log ((∑ a, CA2_7_7I1R5Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_7_7I1R5Mass_sound) (w := CA2_7_7I1R5MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CA2_7_7I1R5MassTerm_sound : CA2_7_7I1R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_7_7I1R5Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_7_7I1R5Mass_sound) CA2_7_7I1R5MassTermLog_sound) (by decide +kernel)
lemma CA2_7_7I1R5H_sound : CA2_7_7I1R5H.Encloses (homogeneousEntropy CA2_7_7I1R5Value) := by
  exact contains_sound (homogeneous_enclosed CA2_7_7I1R5Value CA2_7_7I1R5MassTerm_sound CA2_7_7I1R5Entropy_sound) (by decide +kernel)
lemma CA2_7_7I1R6Raw_sound (a : PairSlot) :
    (CA2_7_7I1R6Raw a).Encloses (CA2_7_7I1R6Value a) := by
  exact residualBall_sound_on (below (shape 2 7 7)) A2_7_7Law (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_7_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 7 7) (show (shape 2 7 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 6 a
lemma CA2_7_7I1R6Certificates_valid :
    CA2_7_7I1R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA2_7_7I1R6P_check : ∀ a : PairSlot, contains (CA2_7_7I1R6Raw a) (CA2_7_7I1R6P a) = true := by
  decide +kernel
lemma CA2_7_7I1R6P_sound (a : PairSlot) :
    (CA2_7_7I1R6P a).Encloses (CA2_7_7I1R6Value a) :=
  contains_sound (CA2_7_7I1R6Raw_sound a) (CA2_7_7I1R6P_check a)
lemma CA2_7_7I1R6Terms_sound (a : PairSlot) :
    (CA2_7_7I1R6Terms a).Encloses (Foundation.entropyTerm (CA2_7_7I1R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_7_7I1R6Certificates_valid
    (CA2_7_7I1R6CertificateIndex a) (CA2_7_7I1R6P_sound a)
lemma CA2_7_7I1R6Entropy_sound : CA2_7_7I1R6Entropy.Encloses (Foundation.finiteEntropy CA2_7_7I1R6Value) := by
  exact contains_sound (entropyPair_enclosed CA2_7_7I1R6Value CA2_7_7I1R6Terms CA2_7_7I1R6Terms_sound) (by decide +kernel)
lemma CA2_7_7I1R6Mass_sound : CA2_7_7I1R6Mass.Encloses (∑ a, CA2_7_7I1R6Value a) := by
  exact contains_sound (pairSumBall_sound CA2_7_7I1R6P CA2_7_7I1R6Value CA2_7_7I1R6P_sound) (by decide +kernel)
lemma CA2_7_7I1R6MassTermLog_sound : CA2_7_7I1R6MassTermLog.Encloses (Real.log ((∑ a, CA2_7_7I1R6Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_7_7I1R6Mass_sound) (w := CA2_7_7I1R6MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CA2_7_7I1R6MassTerm_sound : CA2_7_7I1R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_7_7I1R6Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_7_7I1R6Mass_sound) CA2_7_7I1R6MassTermLog_sound) (by decide +kernel)
lemma CA2_7_7I1R6H_sound : CA2_7_7I1R6H.Encloses (homogeneousEntropy CA2_7_7I1R6Value) := by
  exact contains_sound (homogeneous_enclosed CA2_7_7I1R6Value CA2_7_7I1R6MassTerm_sound CA2_7_7I1R6Entropy_sound) (by decide +kernel)
lemma CA2_7_7I1R7Raw_sound (a : PairSlot) :
    (CA2_7_7I1R7Raw a).Encloses (CA2_7_7I1R7Value a) := by
  exact residualBall_sound_on (below (shape 2 7 7)) A2_7_7Law (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_7_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 7 7) (show (shape 2 7 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 7 a
lemma CA2_7_7I1R7Certificates_valid :
    CA2_7_7I1R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA2_7_7I1R7P_check : ∀ a : PairSlot, contains (CA2_7_7I1R7Raw a) (CA2_7_7I1R7P a) = true := by
  decide +kernel
lemma CA2_7_7I1R7P_sound (a : PairSlot) :
    (CA2_7_7I1R7P a).Encloses (CA2_7_7I1R7Value a) :=
  contains_sound (CA2_7_7I1R7Raw_sound a) (CA2_7_7I1R7P_check a)
lemma CA2_7_7I1R7Terms_sound (a : PairSlot) :
    (CA2_7_7I1R7Terms a).Encloses (Foundation.entropyTerm (CA2_7_7I1R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_7_7I1R7Certificates_valid
    (CA2_7_7I1R7CertificateIndex a) (CA2_7_7I1R7P_sound a)
lemma CA2_7_7I1R7Entropy_sound : CA2_7_7I1R7Entropy.Encloses (Foundation.finiteEntropy CA2_7_7I1R7Value) := by
  exact contains_sound (entropyPair_enclosed CA2_7_7I1R7Value CA2_7_7I1R7Terms CA2_7_7I1R7Terms_sound) (by decide +kernel)
lemma CA2_7_7I1R7Mass_sound : CA2_7_7I1R7Mass.Encloses (∑ a, CA2_7_7I1R7Value a) := by
  exact contains_sound (pairSumBall_sound CA2_7_7I1R7P CA2_7_7I1R7Value CA2_7_7I1R7P_sound) (by decide +kernel)
lemma CA2_7_7I1R7MassTermLog_sound : CA2_7_7I1R7MassTermLog.Encloses (Real.log ((∑ a, CA2_7_7I1R7Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_7_7I1R7Mass_sound) (w := CA2_7_7I1R7MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CA2_7_7I1R7MassTerm_sound : CA2_7_7I1R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_7_7I1R7Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_7_7I1R7Mass_sound) CA2_7_7I1R7MassTermLog_sound) (by decide +kernel)
lemma CA2_7_7I1R7H_sound : CA2_7_7I1R7H.Encloses (homogeneousEntropy CA2_7_7I1R7Value) := by
  exact contains_sound (homogeneous_enclosed CA2_7_7I1R7Value CA2_7_7I1R7MassTerm_sound CA2_7_7I1R7Entropy_sound) (by decide +kernel)
lemma CA2_7_7I1R8Raw_sound (a : PairSlot) :
    (CA2_7_7I1R8Raw a).Encloses (CA2_7_7I1R8Value a) := by
  exact residualBall_sound_on (below (shape 2 7 7)) A2_7_7Law (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_7_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 7 7) (show (shape 2 7 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 8 a
lemma CA2_7_7I1R8Certificates_valid :
    CA2_7_7I1R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA2_7_7I1R8P_check : ∀ a : PairSlot, contains (CA2_7_7I1R8Raw a) (CA2_7_7I1R8P a) = true := by
  decide +kernel
lemma CA2_7_7I1R8P_sound (a : PairSlot) :
    (CA2_7_7I1R8P a).Encloses (CA2_7_7I1R8Value a) :=
  contains_sound (CA2_7_7I1R8Raw_sound a) (CA2_7_7I1R8P_check a)
lemma CA2_7_7I1R8Terms_sound (a : PairSlot) :
    (CA2_7_7I1R8Terms a).Encloses (Foundation.entropyTerm (CA2_7_7I1R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_7_7I1R8Certificates_valid
    (CA2_7_7I1R8CertificateIndex a) (CA2_7_7I1R8P_sound a)
lemma CA2_7_7I1R8Entropy_sound : CA2_7_7I1R8Entropy.Encloses (Foundation.finiteEntropy CA2_7_7I1R8Value) := by
  exact contains_sound (entropyPair_enclosed CA2_7_7I1R8Value CA2_7_7I1R8Terms CA2_7_7I1R8Terms_sound) (by decide +kernel)
lemma CA2_7_7I1R8Mass_sound : CA2_7_7I1R8Mass.Encloses (∑ a, CA2_7_7I1R8Value a) := by
  exact contains_sound (pairSumBall_sound CA2_7_7I1R8P CA2_7_7I1R8Value CA2_7_7I1R8P_sound) (by decide +kernel)
lemma CA2_7_7I1R8MassTerm_sound : CA2_7_7I1R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_7_7I1R8Value a))) :=
  entropyTerm_zero_ball (CA2_7_7I1R8Mass_sound)
lemma CA2_7_7I1R8H_sound : CA2_7_7I1R8H.Encloses (homogeneousEntropy CA2_7_7I1R8Value) := by
  exact contains_sound (homogeneous_enclosed CA2_7_7I1R8Value CA2_7_7I1R8MassTerm_sound CA2_7_7I1R8Entropy_sound) (by decide +kernel)
lemma CA2_7_7I1R9Raw_sound (a : PairSlot) :
    (CA2_7_7I1R9Raw a).Encloses (CA2_7_7I1R9Value a) := by
  exact residualBall_sound_on (below (shape 2 7 7)) A2_7_7Law (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_7_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 7 7) (show (shape 2 7 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 9 a
lemma CA2_7_7I1R9Certificates_valid :
    CA2_7_7I1R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA2_7_7I1R9P_check : ∀ a : PairSlot, contains (CA2_7_7I1R9Raw a) (CA2_7_7I1R9P a) = true := by
  decide +kernel
lemma CA2_7_7I1R9P_sound (a : PairSlot) :
    (CA2_7_7I1R9P a).Encloses (CA2_7_7I1R9Value a) :=
  contains_sound (CA2_7_7I1R9Raw_sound a) (CA2_7_7I1R9P_check a)
lemma CA2_7_7I1R9Terms_sound (a : PairSlot) :
    (CA2_7_7I1R9Terms a).Encloses (Foundation.entropyTerm (CA2_7_7I1R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_7_7I1R9Certificates_valid
    (CA2_7_7I1R9CertificateIndex a) (CA2_7_7I1R9P_sound a)
lemma CA2_7_7I1R9Entropy_sound : CA2_7_7I1R9Entropy.Encloses (Foundation.finiteEntropy CA2_7_7I1R9Value) := by
  exact contains_sound (entropyPair_enclosed CA2_7_7I1R9Value CA2_7_7I1R9Terms CA2_7_7I1R9Terms_sound) (by decide +kernel)
lemma CA2_7_7I1R9Mass_sound : CA2_7_7I1R9Mass.Encloses (∑ a, CA2_7_7I1R9Value a) := by
  exact contains_sound (pairSumBall_sound CA2_7_7I1R9P CA2_7_7I1R9Value CA2_7_7I1R9P_sound) (by decide +kernel)
lemma CA2_7_7I1R9MassTerm_sound : CA2_7_7I1R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_7_7I1R9Value a))) :=
  entropyTerm_zero_ball (CA2_7_7I1R9Mass_sound)
lemma CA2_7_7I1R9H_sound : CA2_7_7I1R9H.Encloses (homogeneousEntropy CA2_7_7I1R9Value) := by
  exact contains_sound (homogeneous_enclosed CA2_7_7I1R9Value CA2_7_7I1R9MassTerm_sound CA2_7_7I1R9Entropy_sound) (by decide +kernel)
lemma CA2_7_7I1R10Raw_sound (a : PairSlot) :
    (CA2_7_7I1R10Raw a).Encloses (CA2_7_7I1R10Value a) := by
  exact residualBall_sound_on (below (shape 2 7 7)) A2_7_7Law (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_7_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 7 7) (show (shape 2 7 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 10 a
lemma CA2_7_7I1R10Certificates_valid :
    CA2_7_7I1R10Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA2_7_7I1R10P_check : ∀ a : PairSlot, contains (CA2_7_7I1R10Raw a) (CA2_7_7I1R10P a) = true := by
  decide +kernel
lemma CA2_7_7I1R10P_sound (a : PairSlot) :
    (CA2_7_7I1R10P a).Encloses (CA2_7_7I1R10Value a) :=
  contains_sound (CA2_7_7I1R10Raw_sound a) (CA2_7_7I1R10P_check a)
lemma CA2_7_7I1R10Terms_sound (a : PairSlot) :
    (CA2_7_7I1R10Terms a).Encloses (Foundation.entropyTerm (CA2_7_7I1R10Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_7_7I1R10Certificates_valid
    (CA2_7_7I1R10CertificateIndex a) (CA2_7_7I1R10P_sound a)
lemma CA2_7_7I1R10Entropy_sound : CA2_7_7I1R10Entropy.Encloses (Foundation.finiteEntropy CA2_7_7I1R10Value) := by
  exact contains_sound (entropyPair_enclosed CA2_7_7I1R10Value CA2_7_7I1R10Terms CA2_7_7I1R10Terms_sound) (by decide +kernel)
lemma CA2_7_7I1R10Mass_sound : CA2_7_7I1R10Mass.Encloses (∑ a, CA2_7_7I1R10Value a) := by
  exact contains_sound (pairSumBall_sound CA2_7_7I1R10P CA2_7_7I1R10Value CA2_7_7I1R10P_sound) (by decide +kernel)
lemma CA2_7_7I1R10MassTerm_sound : CA2_7_7I1R10MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_7_7I1R10Value a))) :=
  entropyTerm_zero_ball (CA2_7_7I1R10Mass_sound)
lemma CA2_7_7I1R10H_sound : CA2_7_7I1R10H.Encloses (homogeneousEntropy CA2_7_7I1R10Value) := by
  exact contains_sound (homogeneous_enclosed CA2_7_7I1R10Value CA2_7_7I1R10MassTerm_sound CA2_7_7I1R10Entropy_sound) (by decide +kernel)
lemma CA2_7_7I1R11Raw_sound (a : PairSlot) :
    (CA2_7_7I1R11Raw a).Encloses (CA2_7_7I1R11Value a) := by
  exact residualBall_sound_on (below (shape 2 7 7)) A2_7_7Law (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_7_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 7 7) (show (shape 2 7 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 11 a
lemma CA2_7_7I1R11Certificates_valid :
    CA2_7_7I1R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA2_7_7I1R11P_check : ∀ a : PairSlot, contains (CA2_7_7I1R11Raw a) (CA2_7_7I1R11P a) = true := by
  decide +kernel
lemma CA2_7_7I1R11P_sound (a : PairSlot) :
    (CA2_7_7I1R11P a).Encloses (CA2_7_7I1R11Value a) :=
  contains_sound (CA2_7_7I1R11Raw_sound a) (CA2_7_7I1R11P_check a)
lemma CA2_7_7I1R11Terms_sound (a : PairSlot) :
    (CA2_7_7I1R11Terms a).Encloses (Foundation.entropyTerm (CA2_7_7I1R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_7_7I1R11Certificates_valid
    (CA2_7_7I1R11CertificateIndex a) (CA2_7_7I1R11P_sound a)
lemma CA2_7_7I1R11Entropy_sound : CA2_7_7I1R11Entropy.Encloses (Foundation.finiteEntropy CA2_7_7I1R11Value) := by
  exact contains_sound (entropyPair_enclosed CA2_7_7I1R11Value CA2_7_7I1R11Terms CA2_7_7I1R11Terms_sound) (by decide +kernel)
lemma CA2_7_7I1R11Mass_sound : CA2_7_7I1R11Mass.Encloses (∑ a, CA2_7_7I1R11Value a) := by
  exact contains_sound (pairSumBall_sound CA2_7_7I1R11P CA2_7_7I1R11Value CA2_7_7I1R11P_sound) (by decide +kernel)
lemma CA2_7_7I1R11MassTerm_sound : CA2_7_7I1R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_7_7I1R11Value a))) :=
  entropyTerm_zero_ball (CA2_7_7I1R11Mass_sound)
lemma CA2_7_7I1R11H_sound : CA2_7_7I1R11H.Encloses (homogeneousEntropy CA2_7_7I1R11Value) := by
  exact contains_sound (homogeneous_enclosed CA2_7_7I1R11Value CA2_7_7I1R11MassTerm_sound CA2_7_7I1R11Entropy_sound) (by decide +kernel)
lemma CA2_7_7I1R12Raw_sound (a : PairSlot) :
    (CA2_7_7I1R12Raw a).Encloses (CA2_7_7I1R12Value a) := by
  exact residualBall_sound_on (below (shape 2 7 7)) A2_7_7Law (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_7_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 7 7) (show (shape 2 7 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 12 a
lemma CA2_7_7I1R12Certificates_valid :
    CA2_7_7I1R12Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA2_7_7I1R12P_check : ∀ a : PairSlot, contains (CA2_7_7I1R12Raw a) (CA2_7_7I1R12P a) = true := by
  decide +kernel
lemma CA2_7_7I1R12P_sound (a : PairSlot) :
    (CA2_7_7I1R12P a).Encloses (CA2_7_7I1R12Value a) :=
  contains_sound (CA2_7_7I1R12Raw_sound a) (CA2_7_7I1R12P_check a)
lemma CA2_7_7I1R12Terms_sound (a : PairSlot) :
    (CA2_7_7I1R12Terms a).Encloses (Foundation.entropyTerm (CA2_7_7I1R12Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_7_7I1R12Certificates_valid
    (CA2_7_7I1R12CertificateIndex a) (CA2_7_7I1R12P_sound a)
lemma CA2_7_7I1R12Entropy_sound : CA2_7_7I1R12Entropy.Encloses (Foundation.finiteEntropy CA2_7_7I1R12Value) := by
  exact contains_sound (entropyPair_enclosed CA2_7_7I1R12Value CA2_7_7I1R12Terms CA2_7_7I1R12Terms_sound) (by decide +kernel)
lemma CA2_7_7I1R12Mass_sound : CA2_7_7I1R12Mass.Encloses (∑ a, CA2_7_7I1R12Value a) := by
  exact contains_sound (pairSumBall_sound CA2_7_7I1R12P CA2_7_7I1R12Value CA2_7_7I1R12P_sound) (by decide +kernel)
lemma CA2_7_7I1R12MassTerm_sound : CA2_7_7I1R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_7_7I1R12Value a))) :=
  entropyTerm_zero_ball (CA2_7_7I1R12Mass_sound)
lemma CA2_7_7I1R12H_sound : CA2_7_7I1R12H.Encloses (homogeneousEntropy CA2_7_7I1R12Value) := by
  exact contains_sound (homogeneous_enclosed CA2_7_7I1R12Value CA2_7_7I1R12MassTerm_sound CA2_7_7I1R12Entropy_sound) (by decide +kernel)
lemma CA2_7_7I1R13Raw_sound (a : PairSlot) :
    (CA2_7_7I1R13Raw a).Encloses (CA2_7_7I1R13Value a) := by
  exact residualBall_sound_on (below (shape 2 7 7)) A2_7_7Law (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_7_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 7 7) (show (shape 2 7 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 13 a
lemma CA2_7_7I1R13Certificates_valid :
    CA2_7_7I1R13Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA2_7_7I1R13P_check : ∀ a : PairSlot, contains (CA2_7_7I1R13Raw a) (CA2_7_7I1R13P a) = true := by
  decide +kernel
lemma CA2_7_7I1R13P_sound (a : PairSlot) :
    (CA2_7_7I1R13P a).Encloses (CA2_7_7I1R13Value a) :=
  contains_sound (CA2_7_7I1R13Raw_sound a) (CA2_7_7I1R13P_check a)
lemma CA2_7_7I1R13Terms_sound (a : PairSlot) :
    (CA2_7_7I1R13Terms a).Encloses (Foundation.entropyTerm (CA2_7_7I1R13Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_7_7I1R13Certificates_valid
    (CA2_7_7I1R13CertificateIndex a) (CA2_7_7I1R13P_sound a)
lemma CA2_7_7I1R13Entropy_sound : CA2_7_7I1R13Entropy.Encloses (Foundation.finiteEntropy CA2_7_7I1R13Value) := by
  exact contains_sound (entropyPair_enclosed CA2_7_7I1R13Value CA2_7_7I1R13Terms CA2_7_7I1R13Terms_sound) (by decide +kernel)
lemma CA2_7_7I1R13Mass_sound : CA2_7_7I1R13Mass.Encloses (∑ a, CA2_7_7I1R13Value a) := by
  exact contains_sound (pairSumBall_sound CA2_7_7I1R13P CA2_7_7I1R13Value CA2_7_7I1R13P_sound) (by decide +kernel)
lemma CA2_7_7I1R13MassTerm_sound : CA2_7_7I1R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_7_7I1R13Value a))) :=
  entropyTerm_zero_ball (CA2_7_7I1R13Mass_sound)
lemma CA2_7_7I1R13H_sound : CA2_7_7I1R13H.Encloses (homogeneousEntropy CA2_7_7I1R13Value) := by
  exact contains_sound (homogeneous_enclosed CA2_7_7I1R13Value CA2_7_7I1R13MassTerm_sound CA2_7_7I1R13Entropy_sound) (by decide +kernel)
lemma CA2_7_7I1R14Raw_sound (a : PairSlot) :
    (CA2_7_7I1R14Raw a).Encloses (CA2_7_7I1R14Value a) := by
  exact residualBall_sound_on (below (shape 2 7 7)) A2_7_7Law (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_7_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 7 7) (show (shape 2 7 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 14 a
lemma CA2_7_7I1R14Certificates_valid :
    CA2_7_7I1R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA2_7_7I1R14P_check : ∀ a : PairSlot, contains (CA2_7_7I1R14Raw a) (CA2_7_7I1R14P a) = true := by
  decide +kernel
lemma CA2_7_7I1R14P_sound (a : PairSlot) :
    (CA2_7_7I1R14P a).Encloses (CA2_7_7I1R14Value a) :=
  contains_sound (CA2_7_7I1R14Raw_sound a) (CA2_7_7I1R14P_check a)
lemma CA2_7_7I1R14Terms_sound (a : PairSlot) :
    (CA2_7_7I1R14Terms a).Encloses (Foundation.entropyTerm (CA2_7_7I1R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_7_7I1R14Certificates_valid
    (CA2_7_7I1R14CertificateIndex a) (CA2_7_7I1R14P_sound a)
lemma CA2_7_7I1R14Entropy_sound : CA2_7_7I1R14Entropy.Encloses (Foundation.finiteEntropy CA2_7_7I1R14Value) := by
  exact contains_sound (entropyPair_enclosed CA2_7_7I1R14Value CA2_7_7I1R14Terms CA2_7_7I1R14Terms_sound) (by decide +kernel)
lemma CA2_7_7I1R14Mass_sound : CA2_7_7I1R14Mass.Encloses (∑ a, CA2_7_7I1R14Value a) := by
  exact contains_sound (pairSumBall_sound CA2_7_7I1R14P CA2_7_7I1R14Value CA2_7_7I1R14P_sound) (by decide +kernel)
lemma CA2_7_7I1R14MassTerm_sound : CA2_7_7I1R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_7_7I1R14Value a))) :=
  entropyTerm_zero_ball (CA2_7_7I1R14Mass_sound)
lemma CA2_7_7I1R14H_sound : CA2_7_7I1R14H.Encloses (homogeneousEntropy CA2_7_7I1R14Value) := by
  exact contains_sound (homogeneous_enclosed CA2_7_7I1R14Value CA2_7_7I1R14MassTerm_sound CA2_7_7I1R14Entropy_sound) (by decide +kernel)
lemma CA2_7_7I1R15Raw_sound (a : PairSlot) :
    (CA2_7_7I1R15Raw a).Encloses (CA2_7_7I1R15Value a) := by
  exact residualBall_sound_on (below (shape 2 7 7)) A2_7_7Law (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_7_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 7 7) (show (shape 2 7 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 15 a
lemma CA2_7_7I1R15Certificates_valid :
    CA2_7_7I1R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA2_7_7I1R15P_check : ∀ a : PairSlot, contains (CA2_7_7I1R15Raw a) (CA2_7_7I1R15P a) = true := by
  decide +kernel
lemma CA2_7_7I1R15P_sound (a : PairSlot) :
    (CA2_7_7I1R15P a).Encloses (CA2_7_7I1R15Value a) :=
  contains_sound (CA2_7_7I1R15Raw_sound a) (CA2_7_7I1R15P_check a)
lemma CA2_7_7I1R15Terms_sound (a : PairSlot) :
    (CA2_7_7I1R15Terms a).Encloses (Foundation.entropyTerm (CA2_7_7I1R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_7_7I1R15Certificates_valid
    (CA2_7_7I1R15CertificateIndex a) (CA2_7_7I1R15P_sound a)
lemma CA2_7_7I1R15Entropy_sound : CA2_7_7I1R15Entropy.Encloses (Foundation.finiteEntropy CA2_7_7I1R15Value) := by
  exact contains_sound (entropyPair_enclosed CA2_7_7I1R15Value CA2_7_7I1R15Terms CA2_7_7I1R15Terms_sound) (by decide +kernel)
lemma CA2_7_7I1R15Mass_sound : CA2_7_7I1R15Mass.Encloses (∑ a, CA2_7_7I1R15Value a) := by
  exact contains_sound (pairSumBall_sound CA2_7_7I1R15P CA2_7_7I1R15Value CA2_7_7I1R15P_sound) (by decide +kernel)
lemma CA2_7_7I1R15MassTerm_sound : CA2_7_7I1R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_7_7I1R15Value a))) :=
  entropyTerm_zero_ball (CA2_7_7I1R15Mass_sound)
lemma CA2_7_7I1R15H_sound : CA2_7_7I1R15H.Encloses (homogeneousEntropy CA2_7_7I1R15Value) := by
  exact contains_sound (homogeneous_enclosed CA2_7_7I1R15Value CA2_7_7I1R15MassTerm_sound CA2_7_7I1R15Entropy_sound) (by decide +kernel)
lemma CA2_7_7I1R16Raw_sound (a : PairSlot) :
    (CA2_7_7I1R16Raw a).Encloses (CA2_7_7I1R16Value a) := by
  exact residualBall_sound_on (below (shape 2 7 7)) A2_7_7Law (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_7_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 7 7) (show (shape 2 7 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 16 a
lemma CA2_7_7I1R16Certificates_valid :
    CA2_7_7I1R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA2_7_7I1R16P_check : ∀ a : PairSlot, contains (CA2_7_7I1R16Raw a) (CA2_7_7I1R16P a) = true := by
  decide +kernel
lemma CA2_7_7I1R16P_sound (a : PairSlot) :
    (CA2_7_7I1R16P a).Encloses (CA2_7_7I1R16Value a) :=
  contains_sound (CA2_7_7I1R16Raw_sound a) (CA2_7_7I1R16P_check a)
lemma CA2_7_7I1R16Terms_sound (a : PairSlot) :
    (CA2_7_7I1R16Terms a).Encloses (Foundation.entropyTerm (CA2_7_7I1R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_7_7I1R16Certificates_valid
    (CA2_7_7I1R16CertificateIndex a) (CA2_7_7I1R16P_sound a)
lemma CA2_7_7I1R16Entropy_sound : CA2_7_7I1R16Entropy.Encloses (Foundation.finiteEntropy CA2_7_7I1R16Value) := by
  exact contains_sound (entropyPair_enclosed CA2_7_7I1R16Value CA2_7_7I1R16Terms CA2_7_7I1R16Terms_sound) (by decide +kernel)
lemma CA2_7_7I1R16Mass_sound : CA2_7_7I1R16Mass.Encloses (∑ a, CA2_7_7I1R16Value a) := by
  exact contains_sound (pairSumBall_sound CA2_7_7I1R16P CA2_7_7I1R16Value CA2_7_7I1R16P_sound) (by decide +kernel)
lemma CA2_7_7I1R16MassTerm_sound : CA2_7_7I1R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_7_7I1R16Value a))) :=
  entropyTerm_zero_ball (CA2_7_7I1R16Mass_sound)
lemma CA2_7_7I1R16H_sound : CA2_7_7I1R16H.Encloses (homogeneousEntropy CA2_7_7I1R16Value) := by
  exact contains_sound (homogeneous_enclosed CA2_7_7I1R16Value CA2_7_7I1R16MassTerm_sound CA2_7_7I1R16Entropy_sound) (by decide +kernel)
lemma CA2_7_7I1ResidualEntropies_sound (k : Fin 17) :
    (CA2_7_7I1ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 2 7 7)) (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) k)) := by
  fin_cases k
  · exact CA2_7_7I1R0H_sound
  · exact CA2_7_7I1R1H_sound
  · exact CA2_7_7I1R2H_sound
  · exact CA2_7_7I1R3H_sound
  · exact CA2_7_7I1R4H_sound
  · exact CA2_7_7I1R5H_sound
  · exact CA2_7_7I1R6H_sound
  · exact CA2_7_7I1R7H_sound
  · exact CA2_7_7I1R8H_sound
  · exact CA2_7_7I1R9H_sound
  · exact CA2_7_7I1R10H_sound
  · exact CA2_7_7I1R11H_sound
  · exact CA2_7_7I1R12H_sound
  · exact CA2_7_7I1R13H_sound
  · exact CA2_7_7I1R14H_sound
  · exact CA2_7_7I1R15H_sound
  · exact CA2_7_7I1R16H_sound
lemma CA2_7_7I1Group_sound_oai : CA2_7_7I1Group.Encloses
    (groupedEntropy (below (shape 2 7 7)) (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CA2_7_7I1Singleton_sound
    (finSumBall_sound 17 CA2_7_7I1ResidualEntropies _ CA2_7_7I1ResidualEntropies_sound)) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_7_7I1Group_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_7_7I1Group_sound_oai
