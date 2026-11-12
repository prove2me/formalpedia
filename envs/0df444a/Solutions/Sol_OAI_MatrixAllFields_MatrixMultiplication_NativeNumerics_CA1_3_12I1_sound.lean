-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_3_12I1_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:44:33.087405+00:00
-- url     : https://prove2.me/submissions/bed21c79-8a90-43df-94ee-c71b374a50dc

import Mathlib
import Definitions.Def_OAIQ254M007
import Definitions.Def_OAIQ254M011
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_mul_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_CompactCertificate_entropyLookup_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_A1_3_12Law_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_3_12I1PairH_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_3_12I1R0H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_3_12I1R10H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_3_12I1R11H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_3_12I1R12H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_3_12I1R13H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_3_12I1R14H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_3_12I1R15P_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_3_12I1R15Terms_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_3_12I1R16H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_3_12I1R1H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_3_12I1R2H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_3_12I1R3H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_3_12I1R4H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_3_12I1R5Raw_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_3_12I1R5Terms_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_3_12I1R6H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_3_12I1R7H_sound
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
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitA1_3_12
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
lemma A1_3_12_below : below (shape 1 3 12) = [
  (shape 0 0 8),
  (shape 0 1 7),
  (shape 0 2 6),
  (shape 0 3 5),
  (shape 1 0 7),
  (shape 1 1 6),
  (shape 1 2 5),
  (shape 1 3 4)] := by decide +kernel

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_3_12I1
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
lemma CA1_3_12I1R5P_check : ∀ a : PairSlot, contains (CA1_3_12I1R5Raw a) (CA1_3_12I1R5P a) = true := by
  decide +kernel
lemma CA1_3_12I1R5P_sound (a : PairSlot) :
    (CA1_3_12I1R5P a).Encloses (CA1_3_12I1R5Value a) :=
  contains_sound (CA1_3_12I1R5Raw_sound a) (CA1_3_12I1R5P_check a)
lemma CA1_3_12I1R5Entropy_sound : CA1_3_12I1R5Entropy.Encloses (Foundation.finiteEntropy CA1_3_12I1R5Value) := by
  exact contains_sound (entropyPair_enclosed CA1_3_12I1R5Value CA1_3_12I1R5Terms CA1_3_12I1R5Terms_sound) (by decide +kernel)
lemma CA1_3_12I1R5Mass_sound : CA1_3_12I1R5Mass.Encloses (∑ a, CA1_3_12I1R5Value a) := by
  exact contains_sound (pairSumBall_sound CA1_3_12I1R5P CA1_3_12I1R5Value CA1_3_12I1R5P_sound) (by decide +kernel)
lemma CA1_3_12I1R5MassTerm_sound : CA1_3_12I1R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_3_12I1R5Value a))) :=
  entropyTerm_zero_ball (CA1_3_12I1R5Mass_sound)
lemma CA1_3_12I1R5H_sound : CA1_3_12I1R5H.Encloses (homogeneousEntropy CA1_3_12I1R5Value) := by
  exact contains_sound (homogeneous_enclosed CA1_3_12I1R5Value CA1_3_12I1R5MassTerm_sound CA1_3_12I1R5Entropy_sound) (by decide +kernel)
lemma CA1_3_12I1R8Raw_sound (a : PairSlot) :
    (CA1_3_12I1R8Raw a).Encloses (CA1_3_12I1R8Value a) := by
  exact residualBall_sound_on (below (shape 1 3 12)) A1_3_12Law (fun u => (stageALaw (shape 1 3 12) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_3_12Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 3 12) (show (shape 1 3 12) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 8 a
lemma CA1_3_12I1R8Certificates_valid :
    CA1_3_12I1R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA1_3_12I1R8P_check : ∀ a : PairSlot, contains (CA1_3_12I1R8Raw a) (CA1_3_12I1R8P a) = true := by
  decide +kernel
lemma CA1_3_12I1R8P_sound (a : PairSlot) :
    (CA1_3_12I1R8P a).Encloses (CA1_3_12I1R8Value a) :=
  contains_sound (CA1_3_12I1R8Raw_sound a) (CA1_3_12I1R8P_check a)
lemma CA1_3_12I1R8Terms_sound (a : PairSlot) :
    (CA1_3_12I1R8Terms a).Encloses (Foundation.entropyTerm (CA1_3_12I1R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_3_12I1R8Certificates_valid
    (CA1_3_12I1R8CertificateIndex a) (CA1_3_12I1R8P_sound a)
lemma CA1_3_12I1R8Entropy_sound : CA1_3_12I1R8Entropy.Encloses (Foundation.finiteEntropy CA1_3_12I1R8Value) := by
  exact contains_sound (entropyPair_enclosed CA1_3_12I1R8Value CA1_3_12I1R8Terms CA1_3_12I1R8Terms_sound) (by decide +kernel)
lemma CA1_3_12I1R8Mass_sound : CA1_3_12I1R8Mass.Encloses (∑ a, CA1_3_12I1R8Value a) := by
  exact contains_sound (pairSumBall_sound CA1_3_12I1R8P CA1_3_12I1R8Value CA1_3_12I1R8P_sound) (by decide +kernel)
lemma CA1_3_12I1R8MassTerm_sound : CA1_3_12I1R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_3_12I1R8Value a))) :=
  entropyTerm_zero_ball (CA1_3_12I1R8Mass_sound)
lemma CA1_3_12I1R8H_sound : CA1_3_12I1R8H.Encloses (homogeneousEntropy CA1_3_12I1R8Value) := by
  exact contains_sound (homogeneous_enclosed CA1_3_12I1R8Value CA1_3_12I1R8MassTerm_sound CA1_3_12I1R8Entropy_sound) (by decide +kernel)
lemma CA1_3_12I1R9Raw_sound (a : PairSlot) :
    (CA1_3_12I1R9Raw a).Encloses (CA1_3_12I1R9Value a) := by
  exact residualBall_sound_on (below (shape 1 3 12)) A1_3_12Law (fun u => (stageALaw (shape 1 3 12) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_3_12Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 3 12) (show (shape 1 3 12) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 9 a
lemma CA1_3_12I1R9Certificates_valid :
    CA1_3_12I1R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA1_3_12I1R9P_check : ∀ a : PairSlot, contains (CA1_3_12I1R9Raw a) (CA1_3_12I1R9P a) = true := by
  decide +kernel
lemma CA1_3_12I1R9P_sound (a : PairSlot) :
    (CA1_3_12I1R9P a).Encloses (CA1_3_12I1R9Value a) :=
  contains_sound (CA1_3_12I1R9Raw_sound a) (CA1_3_12I1R9P_check a)
lemma CA1_3_12I1R9Terms_sound (a : PairSlot) :
    (CA1_3_12I1R9Terms a).Encloses (Foundation.entropyTerm (CA1_3_12I1R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_3_12I1R9Certificates_valid
    (CA1_3_12I1R9CertificateIndex a) (CA1_3_12I1R9P_sound a)
lemma CA1_3_12I1R9Entropy_sound : CA1_3_12I1R9Entropy.Encloses (Foundation.finiteEntropy CA1_3_12I1R9Value) := by
  exact contains_sound (entropyPair_enclosed CA1_3_12I1R9Value CA1_3_12I1R9Terms CA1_3_12I1R9Terms_sound) (by decide +kernel)
lemma CA1_3_12I1R9Mass_sound : CA1_3_12I1R9Mass.Encloses (∑ a, CA1_3_12I1R9Value a) := by
  exact contains_sound (pairSumBall_sound CA1_3_12I1R9P CA1_3_12I1R9Value CA1_3_12I1R9P_sound) (by decide +kernel)
lemma CA1_3_12I1R9MassTerm_sound : CA1_3_12I1R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_3_12I1R9Value a))) :=
  entropyTerm_zero_ball (CA1_3_12I1R9Mass_sound)
lemma CA1_3_12I1R9H_sound : CA1_3_12I1R9H.Encloses (homogeneousEntropy CA1_3_12I1R9Value) := by
  exact contains_sound (homogeneous_enclosed CA1_3_12I1R9Value CA1_3_12I1R9MassTerm_sound CA1_3_12I1R9Entropy_sound) (by decide +kernel)
lemma CA1_3_12I1R15Entropy_sound : CA1_3_12I1R15Entropy.Encloses (Foundation.finiteEntropy CA1_3_12I1R15Value) := by
  exact contains_sound (entropyPair_enclosed CA1_3_12I1R15Value CA1_3_12I1R15Terms CA1_3_12I1R15Terms_sound) (by decide +kernel)
lemma CA1_3_12I1R15Mass_sound : CA1_3_12I1R15Mass.Encloses (∑ a, CA1_3_12I1R15Value a) := by
  exact contains_sound (pairSumBall_sound CA1_3_12I1R15P CA1_3_12I1R15Value CA1_3_12I1R15P_sound) (by decide +kernel)
lemma CA1_3_12I1R15MassTerm_sound : CA1_3_12I1R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_3_12I1R15Value a))) :=
  entropyTerm_zero_ball (CA1_3_12I1R15Mass_sound)
lemma CA1_3_12I1R15H_sound : CA1_3_12I1R15H.Encloses (homogeneousEntropy CA1_3_12I1R15Value) := by
  exact contains_sound (homogeneous_enclosed CA1_3_12I1R15Value CA1_3_12I1R15MassTerm_sound CA1_3_12I1R15Entropy_sound) (by decide +kernel)
lemma CA1_3_12I1ResidualEntropies_sound (k : Fin 17) :
    (CA1_3_12I1ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 1 3 12)) (fun u => (stageALaw (shape 1 3 12) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) k)) := by
  fin_cases k
  · exact CA1_3_12I1R0H_sound
  · exact CA1_3_12I1R1H_sound
  · exact CA1_3_12I1R2H_sound
  · exact CA1_3_12I1R3H_sound
  · exact CA1_3_12I1R4H_sound
  · exact CA1_3_12I1R5H_sound
  · exact CA1_3_12I1R6H_sound
  · exact CA1_3_12I1R7H_sound
  · exact CA1_3_12I1R8H_sound
  · exact CA1_3_12I1R9H_sound
  · exact CA1_3_12I1R10H_sound
  · exact CA1_3_12I1R11H_sound
  · exact CA1_3_12I1R12H_sound
  · exact CA1_3_12I1R13H_sound
  · exact CA1_3_12I1R14H_sound
  · exact CA1_3_12I1R15H_sound
  · exact CA1_3_12I1R16H_sound
lemma CA1_3_12I1Singles_sound (u : Shape) (hu : u ∈ below (shape 1 3 12))
    (hd : designated (Equiv.refl (Fin 3)) 1 u) :
    (CA1_3_12I1Singles u).Encloses (homogeneousEntropy ((fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) u)) := by
  rw [A1_3_12_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 0 8) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 1 7) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 2 6) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 3 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 0 7) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 1 6) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 2 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 3 4) by decide +kernel) hd |>.elim
lemma CA1_3_12I1Singleton_sound : CA1_3_12I1Singleton.Encloses
    (singletonEntropy (below (shape 1 3 12)) (fun u => (stageALaw (shape 1 3 12) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 1 3 12)) A1_3_12Law (fun u => (stageALaw (shape 1 3 12) u : ℝ)) (Equiv.refl (Fin 3)) 1
    CA1_3_12I1Singles (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_3_12Law_sound u) CA1_3_12I1Singles_sound) (by decide +kernel)
lemma CA1_3_12I1Group_sound : CA1_3_12I1Group.Encloses
    (groupedEntropy (below (shape 1 3 12)) (fun u => (stageALaw (shape 1 3 12) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CA1_3_12I1Singleton_sound
    (finSumBall_sound 17 CA1_3_12I1ResidualEntropies _ CA1_3_12I1ResidualEntropies_sound)) (by decide +kernel)

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
lemma CA1_3_12I1_sound_oai : CA1_3_12I1H.Encloses (stageACapacity (shape 1 3 12) 1) := by
  have hb := contains_sound (Ball.add_sound CA1_3_12I1PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CA1_3_12I1Group_sound)))
    (show contains (.add CA1_3_12I1PairH (.neg (.mul (.exact 2) CA1_3_12I1Group))) CA1_3_12I1H = true by decide +kernel)
  simp only [stageACapacity, nativeCapacity,
    show (1 : Fin 3) ≠ 0 by decide, ite_false, if_false]
  change CA1_3_12I1H.Encloses (homogeneousEntropy CA1_3_12I1PairValue - _)
  simpa only [sub_eq_add_neg] using hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_3_12I1_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_3_12I1_sound_oai
