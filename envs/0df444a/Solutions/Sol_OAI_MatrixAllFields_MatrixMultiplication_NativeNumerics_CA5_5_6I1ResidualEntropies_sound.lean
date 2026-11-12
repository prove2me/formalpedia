-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA5_5_6I1ResidualEntropies_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T14:20:44.431681+00:00
-- url     : https://prove2.me/submissions/e518ddd6-8db5-4d25-8594-afbe2609acc6

import Mathlib
import Definitions.Def_OAIQ254M011
import Definitions.Def_OAIQ254M012
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_mul_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_finSumBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_CompactCertificate_entropyLookup_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_A5_5_6Law_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA5_5_6I1R0H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA5_5_6I1R10H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA5_5_6I1R11H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA5_5_6I1R1H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA5_5_6I1R2H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA5_5_6I1R3H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA5_5_6I1R4H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA5_5_6I1R5H_sound
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
lemma CA5_5_6I1R6Raw_sound (a : PairSlot) :
    (CA5_5_6I1R6Raw a).Encloses (CA5_5_6I1R6Value a) := by
  exact residualBall_sound_on (below (shape 5 5 6)) A5_5_6Law (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A5_5_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 5 5 6) (show (shape 5 5 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 6 a
lemma CA5_5_6I1R6Certificates_valid :
    CA5_5_6I1R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA5_5_6I1R6P_check : ∀ a : PairSlot, contains (CA5_5_6I1R6Raw a) (CA5_5_6I1R6P a) = true := by
  decide +kernel
lemma CA5_5_6I1R6P_sound (a : PairSlot) :
    (CA5_5_6I1R6P a).Encloses (CA5_5_6I1R6Value a) :=
  contains_sound (CA5_5_6I1R6Raw_sound a) (CA5_5_6I1R6P_check a)
lemma CA5_5_6I1R6Terms_sound (a : PairSlot) :
    (CA5_5_6I1R6Terms a).Encloses (Foundation.entropyTerm (CA5_5_6I1R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA5_5_6I1R6Certificates_valid
    (CA5_5_6I1R6CertificateIndex a) (CA5_5_6I1R6P_sound a)
lemma CA5_5_6I1R6Entropy_sound : CA5_5_6I1R6Entropy.Encloses (Foundation.finiteEntropy CA5_5_6I1R6Value) := by
  exact contains_sound (entropyPair_enclosed CA5_5_6I1R6Value CA5_5_6I1R6Terms CA5_5_6I1R6Terms_sound) (by decide +kernel)
lemma CA5_5_6I1R6Mass_sound : CA5_5_6I1R6Mass.Encloses (∑ a, CA5_5_6I1R6Value a) := by
  exact contains_sound (pairSumBall_sound CA5_5_6I1R6P CA5_5_6I1R6Value CA5_5_6I1R6P_sound) (by decide +kernel)
lemma CA5_5_6I1R6MassTerm_sound : CA5_5_6I1R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA5_5_6I1R6Value a))) :=
  entropyTerm_zero_ball (CA5_5_6I1R6Mass_sound)
lemma CA5_5_6I1R6H_sound : CA5_5_6I1R6H.Encloses (homogeneousEntropy CA5_5_6I1R6Value) := by
  exact contains_sound (homogeneous_enclosed CA5_5_6I1R6Value CA5_5_6I1R6MassTerm_sound CA5_5_6I1R6Entropy_sound) (by decide +kernel)
lemma CA5_5_6I1R7Raw_sound (a : PairSlot) :
    (CA5_5_6I1R7Raw a).Encloses (CA5_5_6I1R7Value a) := by
  exact residualBall_sound_on (below (shape 5 5 6)) A5_5_6Law (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A5_5_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 5 5 6) (show (shape 5 5 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 7 a
lemma CA5_5_6I1R7Certificates_valid :
    CA5_5_6I1R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA5_5_6I1R7P_check : ∀ a : PairSlot, contains (CA5_5_6I1R7Raw a) (CA5_5_6I1R7P a) = true := by
  decide +kernel
lemma CA5_5_6I1R7P_sound (a : PairSlot) :
    (CA5_5_6I1R7P a).Encloses (CA5_5_6I1R7Value a) :=
  contains_sound (CA5_5_6I1R7Raw_sound a) (CA5_5_6I1R7P_check a)
lemma CA5_5_6I1R7Terms_sound (a : PairSlot) :
    (CA5_5_6I1R7Terms a).Encloses (Foundation.entropyTerm (CA5_5_6I1R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA5_5_6I1R7Certificates_valid
    (CA5_5_6I1R7CertificateIndex a) (CA5_5_6I1R7P_sound a)
lemma CA5_5_6I1R7Entropy_sound : CA5_5_6I1R7Entropy.Encloses (Foundation.finiteEntropy CA5_5_6I1R7Value) := by
  exact contains_sound (entropyPair_enclosed CA5_5_6I1R7Value CA5_5_6I1R7Terms CA5_5_6I1R7Terms_sound) (by decide +kernel)
lemma CA5_5_6I1R7Mass_sound : CA5_5_6I1R7Mass.Encloses (∑ a, CA5_5_6I1R7Value a) := by
  exact contains_sound (pairSumBall_sound CA5_5_6I1R7P CA5_5_6I1R7Value CA5_5_6I1R7P_sound) (by decide +kernel)
lemma CA5_5_6I1R7MassTerm_sound : CA5_5_6I1R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA5_5_6I1R7Value a))) :=
  entropyTerm_zero_ball (CA5_5_6I1R7Mass_sound)
lemma CA5_5_6I1R7H_sound : CA5_5_6I1R7H.Encloses (homogeneousEntropy CA5_5_6I1R7Value) := by
  exact contains_sound (homogeneous_enclosed CA5_5_6I1R7Value CA5_5_6I1R7MassTerm_sound CA5_5_6I1R7Entropy_sound) (by decide +kernel)
lemma CA5_5_6I1R8Raw_sound (a : PairSlot) :
    (CA5_5_6I1R8Raw a).Encloses (CA5_5_6I1R8Value a) := by
  exact residualBall_sound_on (below (shape 5 5 6)) A5_5_6Law (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A5_5_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 5 5 6) (show (shape 5 5 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 8 a
lemma CA5_5_6I1R8Certificates_valid :
    CA5_5_6I1R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA5_5_6I1R8P_check : ∀ a : PairSlot, contains (CA5_5_6I1R8Raw a) (CA5_5_6I1R8P a) = true := by
  decide +kernel
lemma CA5_5_6I1R8P_sound (a : PairSlot) :
    (CA5_5_6I1R8P a).Encloses (CA5_5_6I1R8Value a) :=
  contains_sound (CA5_5_6I1R8Raw_sound a) (CA5_5_6I1R8P_check a)
lemma CA5_5_6I1R8Terms_sound (a : PairSlot) :
    (CA5_5_6I1R8Terms a).Encloses (Foundation.entropyTerm (CA5_5_6I1R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA5_5_6I1R8Certificates_valid
    (CA5_5_6I1R8CertificateIndex a) (CA5_5_6I1R8P_sound a)
lemma CA5_5_6I1R8Entropy_sound : CA5_5_6I1R8Entropy.Encloses (Foundation.finiteEntropy CA5_5_6I1R8Value) := by
  exact contains_sound (entropyPair_enclosed CA5_5_6I1R8Value CA5_5_6I1R8Terms CA5_5_6I1R8Terms_sound) (by decide +kernel)
lemma CA5_5_6I1R8Mass_sound : CA5_5_6I1R8Mass.Encloses (∑ a, CA5_5_6I1R8Value a) := by
  exact contains_sound (pairSumBall_sound CA5_5_6I1R8P CA5_5_6I1R8Value CA5_5_6I1R8P_sound) (by decide +kernel)
lemma CA5_5_6I1R8MassTerm_sound : CA5_5_6I1R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA5_5_6I1R8Value a))) :=
  entropyTerm_zero_ball (CA5_5_6I1R8Mass_sound)
lemma CA5_5_6I1R8H_sound : CA5_5_6I1R8H.Encloses (homogeneousEntropy CA5_5_6I1R8Value) := by
  exact contains_sound (homogeneous_enclosed CA5_5_6I1R8Value CA5_5_6I1R8MassTerm_sound CA5_5_6I1R8Entropy_sound) (by decide +kernel)
lemma CA5_5_6I1R9Raw_sound (a : PairSlot) :
    (CA5_5_6I1R9Raw a).Encloses (CA5_5_6I1R9Value a) := by
  exact residualBall_sound_on (below (shape 5 5 6)) A5_5_6Law (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A5_5_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 5 5 6) (show (shape 5 5 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 9 a
lemma CA5_5_6I1R9Certificates_valid :
    CA5_5_6I1R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA5_5_6I1R9P_check : ∀ a : PairSlot, contains (CA5_5_6I1R9Raw a) (CA5_5_6I1R9P a) = true := by
  decide +kernel
lemma CA5_5_6I1R9P_sound (a : PairSlot) :
    (CA5_5_6I1R9P a).Encloses (CA5_5_6I1R9Value a) :=
  contains_sound (CA5_5_6I1R9Raw_sound a) (CA5_5_6I1R9P_check a)
lemma CA5_5_6I1R9Terms_sound (a : PairSlot) :
    (CA5_5_6I1R9Terms a).Encloses (Foundation.entropyTerm (CA5_5_6I1R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA5_5_6I1R9Certificates_valid
    (CA5_5_6I1R9CertificateIndex a) (CA5_5_6I1R9P_sound a)
lemma CA5_5_6I1R9Entropy_sound : CA5_5_6I1R9Entropy.Encloses (Foundation.finiteEntropy CA5_5_6I1R9Value) := by
  exact contains_sound (entropyPair_enclosed CA5_5_6I1R9Value CA5_5_6I1R9Terms CA5_5_6I1R9Terms_sound) (by decide +kernel)
lemma CA5_5_6I1R9Mass_sound : CA5_5_6I1R9Mass.Encloses (∑ a, CA5_5_6I1R9Value a) := by
  exact contains_sound (pairSumBall_sound CA5_5_6I1R9P CA5_5_6I1R9Value CA5_5_6I1R9P_sound) (by decide +kernel)
lemma CA5_5_6I1R9MassTerm_sound : CA5_5_6I1R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA5_5_6I1R9Value a))) :=
  entropyTerm_zero_ball (CA5_5_6I1R9Mass_sound)
lemma CA5_5_6I1R9H_sound : CA5_5_6I1R9H.Encloses (homogeneousEntropy CA5_5_6I1R9Value) := by
  exact contains_sound (homogeneous_enclosed CA5_5_6I1R9Value CA5_5_6I1R9MassTerm_sound CA5_5_6I1R9Entropy_sound) (by decide +kernel)
lemma CA5_5_6I1R12Raw_sound (a : PairSlot) :
    (CA5_5_6I1R12Raw a).Encloses (CA5_5_6I1R12Value a) := by
  exact residualBall_sound_on (below (shape 5 5 6)) A5_5_6Law (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A5_5_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 5 5 6) (show (shape 5 5 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 12 a
lemma CA5_5_6I1R12Certificates_valid :
    CA5_5_6I1R12Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA5_5_6I1R12P_check : ∀ a : PairSlot, contains (CA5_5_6I1R12Raw a) (CA5_5_6I1R12P a) = true := by
  decide +kernel
lemma CA5_5_6I1R12P_sound (a : PairSlot) :
    (CA5_5_6I1R12P a).Encloses (CA5_5_6I1R12Value a) :=
  contains_sound (CA5_5_6I1R12Raw_sound a) (CA5_5_6I1R12P_check a)
lemma CA5_5_6I1R12Terms_sound (a : PairSlot) :
    (CA5_5_6I1R12Terms a).Encloses (Foundation.entropyTerm (CA5_5_6I1R12Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA5_5_6I1R12Certificates_valid
    (CA5_5_6I1R12CertificateIndex a) (CA5_5_6I1R12P_sound a)
lemma CA5_5_6I1R12Entropy_sound : CA5_5_6I1R12Entropy.Encloses (Foundation.finiteEntropy CA5_5_6I1R12Value) := by
  exact contains_sound (entropyPair_enclosed CA5_5_6I1R12Value CA5_5_6I1R12Terms CA5_5_6I1R12Terms_sound) (by decide +kernel)
lemma CA5_5_6I1R12Mass_sound : CA5_5_6I1R12Mass.Encloses (∑ a, CA5_5_6I1R12Value a) := by
  exact contains_sound (pairSumBall_sound CA5_5_6I1R12P CA5_5_6I1R12Value CA5_5_6I1R12P_sound) (by decide +kernel)
lemma CA5_5_6I1R12MassTerm_sound : CA5_5_6I1R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA5_5_6I1R12Value a))) :=
  entropyTerm_zero_ball (CA5_5_6I1R12Mass_sound)
lemma CA5_5_6I1R12H_sound : CA5_5_6I1R12H.Encloses (homogeneousEntropy CA5_5_6I1R12Value) := by
  exact contains_sound (homogeneous_enclosed CA5_5_6I1R12Value CA5_5_6I1R12MassTerm_sound CA5_5_6I1R12Entropy_sound) (by decide +kernel)
lemma CA5_5_6I1R13Raw_sound (a : PairSlot) :
    (CA5_5_6I1R13Raw a).Encloses (CA5_5_6I1R13Value a) := by
  exact residualBall_sound_on (below (shape 5 5 6)) A5_5_6Law (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A5_5_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 5 5 6) (show (shape 5 5 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 13 a
lemma CA5_5_6I1R13Certificates_valid :
    CA5_5_6I1R13Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA5_5_6I1R13P_check : ∀ a : PairSlot, contains (CA5_5_6I1R13Raw a) (CA5_5_6I1R13P a) = true := by
  decide +kernel
lemma CA5_5_6I1R13P_sound (a : PairSlot) :
    (CA5_5_6I1R13P a).Encloses (CA5_5_6I1R13Value a) :=
  contains_sound (CA5_5_6I1R13Raw_sound a) (CA5_5_6I1R13P_check a)
lemma CA5_5_6I1R13Terms_sound (a : PairSlot) :
    (CA5_5_6I1R13Terms a).Encloses (Foundation.entropyTerm (CA5_5_6I1R13Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA5_5_6I1R13Certificates_valid
    (CA5_5_6I1R13CertificateIndex a) (CA5_5_6I1R13P_sound a)
lemma CA5_5_6I1R13Entropy_sound : CA5_5_6I1R13Entropy.Encloses (Foundation.finiteEntropy CA5_5_6I1R13Value) := by
  exact contains_sound (entropyPair_enclosed CA5_5_6I1R13Value CA5_5_6I1R13Terms CA5_5_6I1R13Terms_sound) (by decide +kernel)
lemma CA5_5_6I1R13Mass_sound : CA5_5_6I1R13Mass.Encloses (∑ a, CA5_5_6I1R13Value a) := by
  exact contains_sound (pairSumBall_sound CA5_5_6I1R13P CA5_5_6I1R13Value CA5_5_6I1R13P_sound) (by decide +kernel)
lemma CA5_5_6I1R13MassTerm_sound : CA5_5_6I1R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA5_5_6I1R13Value a))) :=
  entropyTerm_zero_ball (CA5_5_6I1R13Mass_sound)
lemma CA5_5_6I1R13H_sound : CA5_5_6I1R13H.Encloses (homogeneousEntropy CA5_5_6I1R13Value) := by
  exact contains_sound (homogeneous_enclosed CA5_5_6I1R13Value CA5_5_6I1R13MassTerm_sound CA5_5_6I1R13Entropy_sound) (by decide +kernel)
lemma CA5_5_6I1R14Raw_sound (a : PairSlot) :
    (CA5_5_6I1R14Raw a).Encloses (CA5_5_6I1R14Value a) := by
  exact residualBall_sound_on (below (shape 5 5 6)) A5_5_6Law (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A5_5_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 5 5 6) (show (shape 5 5 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 14 a
lemma CA5_5_6I1R14Certificates_valid :
    CA5_5_6I1R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA5_5_6I1R14P_check : ∀ a : PairSlot, contains (CA5_5_6I1R14Raw a) (CA5_5_6I1R14P a) = true := by
  decide +kernel
lemma CA5_5_6I1R14P_sound (a : PairSlot) :
    (CA5_5_6I1R14P a).Encloses (CA5_5_6I1R14Value a) :=
  contains_sound (CA5_5_6I1R14Raw_sound a) (CA5_5_6I1R14P_check a)
lemma CA5_5_6I1R14Terms_sound (a : PairSlot) :
    (CA5_5_6I1R14Terms a).Encloses (Foundation.entropyTerm (CA5_5_6I1R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA5_5_6I1R14Certificates_valid
    (CA5_5_6I1R14CertificateIndex a) (CA5_5_6I1R14P_sound a)
lemma CA5_5_6I1R14Entropy_sound : CA5_5_6I1R14Entropy.Encloses (Foundation.finiteEntropy CA5_5_6I1R14Value) := by
  exact contains_sound (entropyPair_enclosed CA5_5_6I1R14Value CA5_5_6I1R14Terms CA5_5_6I1R14Terms_sound) (by decide +kernel)
lemma CA5_5_6I1R14Mass_sound : CA5_5_6I1R14Mass.Encloses (∑ a, CA5_5_6I1R14Value a) := by
  exact contains_sound (pairSumBall_sound CA5_5_6I1R14P CA5_5_6I1R14Value CA5_5_6I1R14P_sound) (by decide +kernel)
lemma CA5_5_6I1R14MassTerm_sound : CA5_5_6I1R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA5_5_6I1R14Value a))) :=
  entropyTerm_zero_ball (CA5_5_6I1R14Mass_sound)
lemma CA5_5_6I1R14H_sound : CA5_5_6I1R14H.Encloses (homogeneousEntropy CA5_5_6I1R14Value) := by
  exact contains_sound (homogeneous_enclosed CA5_5_6I1R14Value CA5_5_6I1R14MassTerm_sound CA5_5_6I1R14Entropy_sound) (by decide +kernel)
lemma CA5_5_6I1R15Raw_sound (a : PairSlot) :
    (CA5_5_6I1R15Raw a).Encloses (CA5_5_6I1R15Value a) := by
  exact residualBall_sound_on (below (shape 5 5 6)) A5_5_6Law (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A5_5_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 5 5 6) (show (shape 5 5 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 15 a
lemma CA5_5_6I1R15Certificates_valid :
    CA5_5_6I1R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA5_5_6I1R15P_check : ∀ a : PairSlot, contains (CA5_5_6I1R15Raw a) (CA5_5_6I1R15P a) = true := by
  decide +kernel
lemma CA5_5_6I1R15P_sound (a : PairSlot) :
    (CA5_5_6I1R15P a).Encloses (CA5_5_6I1R15Value a) :=
  contains_sound (CA5_5_6I1R15Raw_sound a) (CA5_5_6I1R15P_check a)
lemma CA5_5_6I1R15Terms_sound (a : PairSlot) :
    (CA5_5_6I1R15Terms a).Encloses (Foundation.entropyTerm (CA5_5_6I1R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA5_5_6I1R15Certificates_valid
    (CA5_5_6I1R15CertificateIndex a) (CA5_5_6I1R15P_sound a)
lemma CA5_5_6I1R15Entropy_sound : CA5_5_6I1R15Entropy.Encloses (Foundation.finiteEntropy CA5_5_6I1R15Value) := by
  exact contains_sound (entropyPair_enclosed CA5_5_6I1R15Value CA5_5_6I1R15Terms CA5_5_6I1R15Terms_sound) (by decide +kernel)
lemma CA5_5_6I1R15Mass_sound : CA5_5_6I1R15Mass.Encloses (∑ a, CA5_5_6I1R15Value a) := by
  exact contains_sound (pairSumBall_sound CA5_5_6I1R15P CA5_5_6I1R15Value CA5_5_6I1R15P_sound) (by decide +kernel)
lemma CA5_5_6I1R15MassTerm_sound : CA5_5_6I1R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA5_5_6I1R15Value a))) :=
  entropyTerm_zero_ball (CA5_5_6I1R15Mass_sound)
lemma CA5_5_6I1R15H_sound : CA5_5_6I1R15H.Encloses (homogeneousEntropy CA5_5_6I1R15Value) := by
  exact contains_sound (homogeneous_enclosed CA5_5_6I1R15Value CA5_5_6I1R15MassTerm_sound CA5_5_6I1R15Entropy_sound) (by decide +kernel)
lemma CA5_5_6I1R16Raw_sound (a : PairSlot) :
    (CA5_5_6I1R16Raw a).Encloses (CA5_5_6I1R16Value a) := by
  exact residualBall_sound_on (below (shape 5 5 6)) A5_5_6Law (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A5_5_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 5 5 6) (show (shape 5 5 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 16 a
lemma CA5_5_6I1R16Certificates_valid :
    CA5_5_6I1R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA5_5_6I1R16P_check : ∀ a : PairSlot, contains (CA5_5_6I1R16Raw a) (CA5_5_6I1R16P a) = true := by
  decide +kernel
lemma CA5_5_6I1R16P_sound (a : PairSlot) :
    (CA5_5_6I1R16P a).Encloses (CA5_5_6I1R16Value a) :=
  contains_sound (CA5_5_6I1R16Raw_sound a) (CA5_5_6I1R16P_check a)
lemma CA5_5_6I1R16Terms_sound (a : PairSlot) :
    (CA5_5_6I1R16Terms a).Encloses (Foundation.entropyTerm (CA5_5_6I1R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA5_5_6I1R16Certificates_valid
    (CA5_5_6I1R16CertificateIndex a) (CA5_5_6I1R16P_sound a)
lemma CA5_5_6I1R16Entropy_sound : CA5_5_6I1R16Entropy.Encloses (Foundation.finiteEntropy CA5_5_6I1R16Value) := by
  exact contains_sound (entropyPair_enclosed CA5_5_6I1R16Value CA5_5_6I1R16Terms CA5_5_6I1R16Terms_sound) (by decide +kernel)
lemma CA5_5_6I1R16Mass_sound : CA5_5_6I1R16Mass.Encloses (∑ a, CA5_5_6I1R16Value a) := by
  exact contains_sound (pairSumBall_sound CA5_5_6I1R16P CA5_5_6I1R16Value CA5_5_6I1R16P_sound) (by decide +kernel)
lemma CA5_5_6I1R16MassTerm_sound : CA5_5_6I1R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA5_5_6I1R16Value a))) :=
  entropyTerm_zero_ball (CA5_5_6I1R16Mass_sound)
lemma CA5_5_6I1R16H_sound : CA5_5_6I1R16H.Encloses (homogeneousEntropy CA5_5_6I1R16Value) := by
  exact contains_sound (homogeneous_enclosed CA5_5_6I1R16Value CA5_5_6I1R16MassTerm_sound CA5_5_6I1R16Entropy_sound) (by decide +kernel)
lemma CA5_5_6I1ResidualEntropies_sound_oai (k : Fin 17) :
    (CA5_5_6I1ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 5 5 6)) (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) k)) := by
  fin_cases k
  · exact CA5_5_6I1R0H_sound
  · exact CA5_5_6I1R1H_sound
  · exact CA5_5_6I1R2H_sound
  · exact CA5_5_6I1R3H_sound
  · exact CA5_5_6I1R4H_sound
  · exact CA5_5_6I1R5H_sound
  · exact CA5_5_6I1R6H_sound
  · exact CA5_5_6I1R7H_sound
  · exact CA5_5_6I1R8H_sound
  · exact CA5_5_6I1R9H_sound
  · exact CA5_5_6I1R10H_sound
  · exact CA5_5_6I1R11H_sound
  · exact CA5_5_6I1R12H_sound
  · exact CA5_5_6I1R13H_sound
  · exact CA5_5_6I1R14H_sound
  · exact CA5_5_6I1R15H_sound
  · exact CA5_5_6I1R16H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA5_5_6I1ResidualEntropies_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA5_5_6I1ResidualEntropies_sound_oai
