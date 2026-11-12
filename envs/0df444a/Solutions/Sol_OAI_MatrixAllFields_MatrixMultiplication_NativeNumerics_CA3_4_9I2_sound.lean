-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_4_9I2_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T14:10:18.712441+00:00
-- url     : https://prove2.me/submissions/c3548523-d4ab-410d-800c-badafb9854a3

import Mathlib
import Definitions.Def_OAIQ254M011
import Definitions.Def_OAIQ254M012
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_inv_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_mul_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkLog_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_finSumBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_CompactCertificate_entropyLookup_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_A3_4_9Den_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_A3_4_9Raw_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA3_4_9I2PairH_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA3_4_9I2R0H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA3_4_9I2R10H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA3_4_9I2R11H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA3_4_9I2R12H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA3_4_9I2R13H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA3_4_9I2R14H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA3_4_9I2R15H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA3_4_9I2R16H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA3_4_9I2R7H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA3_4_9I2Singles_sound
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
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitA3_4_9
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
lemma A3_4_9_below : below (shape 3 4 9) = [
  (shape 0 0 8),
  (shape 0 1 7),
  (shape 0 2 6),
  (shape 0 3 5),
  (shape 0 4 4),
  (shape 1 0 7),
  (shape 1 1 6),
  (shape 1 2 5),
  (shape 1 3 4),
  (shape 1 4 3),
  (shape 2 0 6),
  (shape 2 1 5),
  (shape 2 2 4),
  (shape 2 3 3),
  (shape 2 4 2),
  (shape 3 0 5),
  (shape 3 1 4),
  (shape 3 2 3),
  (shape 3 3 2),
  (shape 3 4 1)] := by decide +kernel
lemma A3_4_9Den_positive : 0 < A3_4_9Den.lower := by decide +kernel
lemma A3_4_9Law_check_0_0_8 : contains (.mul (A3_4_9Raw (shape 0 0 8)) (.inv A3_4_9Den)) (A3_4_9Table (shape 0 0 8)) = true := by decide +kernel
lemma A3_4_9Law_check_0_1_7 : contains (.mul (A3_4_9Raw (shape 0 1 7)) (.inv A3_4_9Den)) (A3_4_9Table (shape 0 1 7)) = true := by decide +kernel
lemma A3_4_9Law_check_0_2_6 : contains (.mul (A3_4_9Raw (shape 0 2 6)) (.inv A3_4_9Den)) (A3_4_9Table (shape 0 2 6)) = true := by decide +kernel
lemma A3_4_9Law_check_0_3_5 : contains (.mul (A3_4_9Raw (shape 0 3 5)) (.inv A3_4_9Den)) (A3_4_9Table (shape 0 3 5)) = true := by decide +kernel
lemma A3_4_9Law_check_0_4_4 : contains (.mul (A3_4_9Raw (shape 0 4 4)) (.inv A3_4_9Den)) (A3_4_9Table (shape 0 4 4)) = true := by decide +kernel
lemma A3_4_9Law_check_1_0_7 : contains (.mul (A3_4_9Raw (shape 1 0 7)) (.inv A3_4_9Den)) (A3_4_9Table (shape 1 0 7)) = true := by decide +kernel
lemma A3_4_9Law_check_1_1_6 : contains (.mul (A3_4_9Raw (shape 1 1 6)) (.inv A3_4_9Den)) (A3_4_9Table (shape 1 1 6)) = true := by decide +kernel
lemma A3_4_9Law_check_1_2_5 : contains (.mul (A3_4_9Raw (shape 1 2 5)) (.inv A3_4_9Den)) (A3_4_9Table (shape 1 2 5)) = true := by decide +kernel
lemma A3_4_9Law_check_1_3_4 : contains (.mul (A3_4_9Raw (shape 1 3 4)) (.inv A3_4_9Den)) (A3_4_9Table (shape 1 3 4)) = true := by decide +kernel
lemma A3_4_9Law_check_1_4_3 : contains (.mul (A3_4_9Raw (shape 1 4 3)) (.inv A3_4_9Den)) (A3_4_9Table (shape 1 4 3)) = true := by decide +kernel
lemma A3_4_9Law_check_2_0_6 : contains (.mul (A3_4_9Raw (shape 2 0 6)) (.inv A3_4_9Den)) (A3_4_9Table (shape 2 0 6)) = true := by decide +kernel
lemma A3_4_9Law_check_2_1_5 : contains (.mul (A3_4_9Raw (shape 2 1 5)) (.inv A3_4_9Den)) (A3_4_9Table (shape 2 1 5)) = true := by decide +kernel
lemma A3_4_9Law_check_2_2_4 : contains (.mul (A3_4_9Raw (shape 2 2 4)) (.inv A3_4_9Den)) (A3_4_9Table (shape 2 2 4)) = true := by decide +kernel
lemma A3_4_9Law_check_2_3_3 : contains (.mul (A3_4_9Raw (shape 2 3 3)) (.inv A3_4_9Den)) (A3_4_9Table (shape 2 3 3)) = true := by decide +kernel
lemma A3_4_9Law_check_2_4_2 : contains (.mul (A3_4_9Raw (shape 2 4 2)) (.inv A3_4_9Den)) (A3_4_9Table (shape 2 4 2)) = true := by decide +kernel
lemma A3_4_9Law_check_3_0_5 : contains (.mul (A3_4_9Raw (shape 3 0 5)) (.inv A3_4_9Den)) (A3_4_9Table (shape 3 0 5)) = true := by decide +kernel
lemma A3_4_9Law_check_3_1_4 : contains (.mul (A3_4_9Raw (shape 3 1 4)) (.inv A3_4_9Den)) (A3_4_9Table (shape 3 1 4)) = true := by decide +kernel
lemma A3_4_9Law_check_3_2_3 : contains (.mul (A3_4_9Raw (shape 3 2 3)) (.inv A3_4_9Den)) (A3_4_9Table (shape 3 2 3)) = true := by decide +kernel
lemma A3_4_9Law_check_3_3_2 : contains (.mul (A3_4_9Raw (shape 3 3 2)) (.inv A3_4_9Den)) (A3_4_9Table (shape 3 3 2)) = true := by decide +kernel
lemma A3_4_9Law_check_3_4_1 : contains (.mul (A3_4_9Raw (shape 3 4 1)) (.inv A3_4_9Den)) (A3_4_9Table (shape 3 4 1)) = true := by decide +kernel
lemma A3_4_9Law_check (u : Shape) (hu : u ∈ below (shape 3 4 9)) :
    contains (.mul (A3_4_9Raw u) (.inv A3_4_9Den)) (A3_4_9Table u) = true := by
  rw [A3_4_9_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A3_4_9Law_check_0_0_8
  · exact A3_4_9Law_check_0_1_7
  · exact A3_4_9Law_check_0_2_6
  · exact A3_4_9Law_check_0_3_5
  · exact A3_4_9Law_check_0_4_4
  · exact A3_4_9Law_check_1_0_7
  · exact A3_4_9Law_check_1_1_6
  · exact A3_4_9Law_check_1_2_5
  · exact A3_4_9Law_check_1_3_4
  · exact A3_4_9Law_check_1_4_3
  · exact A3_4_9Law_check_2_0_6
  · exact A3_4_9Law_check_2_1_5
  · exact A3_4_9Law_check_2_2_4
  · exact A3_4_9Law_check_2_3_3
  · exact A3_4_9Law_check_2_4_2
  · exact A3_4_9Law_check_3_0_5
  · exact A3_4_9Law_check_3_1_4
  · exact A3_4_9Law_check_3_2_3
  · exact A3_4_9Law_check_3_3_2
  · exact A3_4_9Law_check_3_4_1
lemma A3_4_9Law_sound (u : Shape) :
    (A3_4_9Law u).Encloses (stageALaw (shape 3 4 9) u : ℝ) := by
  by_cases hu : u ∈ below (shape 3 4 9)
  · have h := contains_sound (Ball.mul_sound (A3_4_9Raw_sound u hu)
      (Ball.inv_sound A3_4_9Den_sound A3_4_9Den_positive)) (A3_4_9Law_check u hu)
    simpa only [A3_4_9Law, hu, ite_true, if_true, stageALaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [A3_4_9Law, hu, ite_false, if_false, stageALaw, splitLaw, Rat.cast_zero]
    simpa only [Rat.cast_zero] using Ball.exact_sound 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA3_4_9I2
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
lemma CA3_4_9I2R1Raw_sound (a : PairSlot) :
    (CA3_4_9I2R1Raw a).Encloses (CA3_4_9I2R1Value a) := by
  exact residualBall_sound_on (below (shape 3 4 9)) A3_4_9Law (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_4_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 4 9) (show (shape 3 4 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 1 a
lemma CA3_4_9I2R1Certificates_valid :
    CA3_4_9I2R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA3_4_9I2R1P_check : ∀ a : PairSlot, contains (CA3_4_9I2R1Raw a) (CA3_4_9I2R1P a) = true := by
  decide +kernel
lemma CA3_4_9I2R1P_sound (a : PairSlot) :
    (CA3_4_9I2R1P a).Encloses (CA3_4_9I2R1Value a) :=
  contains_sound (CA3_4_9I2R1Raw_sound a) (CA3_4_9I2R1P_check a)
lemma CA3_4_9I2R1Terms_sound (a : PairSlot) :
    (CA3_4_9I2R1Terms a).Encloses (Foundation.entropyTerm (CA3_4_9I2R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_4_9I2R1Certificates_valid
    (CA3_4_9I2R1CertificateIndex a) (CA3_4_9I2R1P_sound a)
lemma CA3_4_9I2R1Entropy_sound : CA3_4_9I2R1Entropy.Encloses (Foundation.finiteEntropy CA3_4_9I2R1Value) := by
  exact contains_sound (entropyPair_enclosed CA3_4_9I2R1Value CA3_4_9I2R1Terms CA3_4_9I2R1Terms_sound) (by decide +kernel)
lemma CA3_4_9I2R1Mass_sound : CA3_4_9I2R1Mass.Encloses (∑ a, CA3_4_9I2R1Value a) := by
  exact contains_sound (pairSumBall_sound CA3_4_9I2R1P CA3_4_9I2R1Value CA3_4_9I2R1P_sound) (by decide +kernel)
lemma CA3_4_9I2R1MassTermLog_sound : CA3_4_9I2R1MassTermLog.Encloses (Real.log ((∑ a, CA3_4_9I2R1Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_4_9I2R1Mass_sound) (w := CA3_4_9I2R1MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CA3_4_9I2R1MassTerm_sound : CA3_4_9I2R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_4_9I2R1Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_4_9I2R1Mass_sound) CA3_4_9I2R1MassTermLog_sound) (by decide +kernel)
lemma CA3_4_9I2R1H_sound : CA3_4_9I2R1H.Encloses (homogeneousEntropy CA3_4_9I2R1Value) := by
  exact contains_sound (homogeneous_enclosed CA3_4_9I2R1Value CA3_4_9I2R1MassTerm_sound CA3_4_9I2R1Entropy_sound) (by decide +kernel)
lemma CA3_4_9I2R2Raw_sound (a : PairSlot) :
    (CA3_4_9I2R2Raw a).Encloses (CA3_4_9I2R2Value a) := by
  exact residualBall_sound_on (below (shape 3 4 9)) A3_4_9Law (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_4_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 4 9) (show (shape 3 4 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 2 a
lemma CA3_4_9I2R2Certificates_valid :
    CA3_4_9I2R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA3_4_9I2R2P_check : ∀ a : PairSlot, contains (CA3_4_9I2R2Raw a) (CA3_4_9I2R2P a) = true := by
  decide +kernel
lemma CA3_4_9I2R2P_sound (a : PairSlot) :
    (CA3_4_9I2R2P a).Encloses (CA3_4_9I2R2Value a) :=
  contains_sound (CA3_4_9I2R2Raw_sound a) (CA3_4_9I2R2P_check a)
lemma CA3_4_9I2R2Terms_sound (a : PairSlot) :
    (CA3_4_9I2R2Terms a).Encloses (Foundation.entropyTerm (CA3_4_9I2R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_4_9I2R2Certificates_valid
    (CA3_4_9I2R2CertificateIndex a) (CA3_4_9I2R2P_sound a)
lemma CA3_4_9I2R2Entropy_sound : CA3_4_9I2R2Entropy.Encloses (Foundation.finiteEntropy CA3_4_9I2R2Value) := by
  exact contains_sound (entropyPair_enclosed CA3_4_9I2R2Value CA3_4_9I2R2Terms CA3_4_9I2R2Terms_sound) (by decide +kernel)
lemma CA3_4_9I2R2Mass_sound : CA3_4_9I2R2Mass.Encloses (∑ a, CA3_4_9I2R2Value a) := by
  exact contains_sound (pairSumBall_sound CA3_4_9I2R2P CA3_4_9I2R2Value CA3_4_9I2R2P_sound) (by decide +kernel)
lemma CA3_4_9I2R2MassTermLog_sound : CA3_4_9I2R2MassTermLog.Encloses (Real.log ((∑ a, CA3_4_9I2R2Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_4_9I2R2Mass_sound) (w := CA3_4_9I2R2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CA3_4_9I2R2MassTerm_sound : CA3_4_9I2R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_4_9I2R2Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_4_9I2R2Mass_sound) CA3_4_9I2R2MassTermLog_sound) (by decide +kernel)
lemma CA3_4_9I2R2H_sound : CA3_4_9I2R2H.Encloses (homogeneousEntropy CA3_4_9I2R2Value) := by
  exact contains_sound (homogeneous_enclosed CA3_4_9I2R2Value CA3_4_9I2R2MassTerm_sound CA3_4_9I2R2Entropy_sound) (by decide +kernel)
lemma CA3_4_9I2R3Raw_sound (a : PairSlot) :
    (CA3_4_9I2R3Raw a).Encloses (CA3_4_9I2R3Value a) := by
  exact residualBall_sound_on (below (shape 3 4 9)) A3_4_9Law (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_4_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 4 9) (show (shape 3 4 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 3 a
lemma CA3_4_9I2R3Certificates_valid :
    CA3_4_9I2R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA3_4_9I2R3P_check : ∀ a : PairSlot, contains (CA3_4_9I2R3Raw a) (CA3_4_9I2R3P a) = true := by
  decide +kernel
lemma CA3_4_9I2R3P_sound (a : PairSlot) :
    (CA3_4_9I2R3P a).Encloses (CA3_4_9I2R3Value a) :=
  contains_sound (CA3_4_9I2R3Raw_sound a) (CA3_4_9I2R3P_check a)
lemma CA3_4_9I2R3Terms_sound (a : PairSlot) :
    (CA3_4_9I2R3Terms a).Encloses (Foundation.entropyTerm (CA3_4_9I2R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_4_9I2R3Certificates_valid
    (CA3_4_9I2R3CertificateIndex a) (CA3_4_9I2R3P_sound a)
lemma CA3_4_9I2R3Entropy_sound : CA3_4_9I2R3Entropy.Encloses (Foundation.finiteEntropy CA3_4_9I2R3Value) := by
  exact contains_sound (entropyPair_enclosed CA3_4_9I2R3Value CA3_4_9I2R3Terms CA3_4_9I2R3Terms_sound) (by decide +kernel)
lemma CA3_4_9I2R3Mass_sound : CA3_4_9I2R3Mass.Encloses (∑ a, CA3_4_9I2R3Value a) := by
  exact contains_sound (pairSumBall_sound CA3_4_9I2R3P CA3_4_9I2R3Value CA3_4_9I2R3P_sound) (by decide +kernel)
lemma CA3_4_9I2R3MassTermLog_sound : CA3_4_9I2R3MassTermLog.Encloses (Real.log ((∑ a, CA3_4_9I2R3Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_4_9I2R3Mass_sound) (w := CA3_4_9I2R3MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CA3_4_9I2R3MassTerm_sound : CA3_4_9I2R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_4_9I2R3Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_4_9I2R3Mass_sound) CA3_4_9I2R3MassTermLog_sound) (by decide +kernel)
lemma CA3_4_9I2R3H_sound : CA3_4_9I2R3H.Encloses (homogeneousEntropy CA3_4_9I2R3Value) := by
  exact contains_sound (homogeneous_enclosed CA3_4_9I2R3Value CA3_4_9I2R3MassTerm_sound CA3_4_9I2R3Entropy_sound) (by decide +kernel)
lemma CA3_4_9I2R4Raw_sound (a : PairSlot) :
    (CA3_4_9I2R4Raw a).Encloses (CA3_4_9I2R4Value a) := by
  exact residualBall_sound_on (below (shape 3 4 9)) A3_4_9Law (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_4_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 4 9) (show (shape 3 4 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 4 a
lemma CA3_4_9I2R4Certificates_valid :
    CA3_4_9I2R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA3_4_9I2R4P_check : ∀ a : PairSlot, contains (CA3_4_9I2R4Raw a) (CA3_4_9I2R4P a) = true := by
  decide +kernel
lemma CA3_4_9I2R4P_sound (a : PairSlot) :
    (CA3_4_9I2R4P a).Encloses (CA3_4_9I2R4Value a) :=
  contains_sound (CA3_4_9I2R4Raw_sound a) (CA3_4_9I2R4P_check a)
lemma CA3_4_9I2R4Terms_sound (a : PairSlot) :
    (CA3_4_9I2R4Terms a).Encloses (Foundation.entropyTerm (CA3_4_9I2R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_4_9I2R4Certificates_valid
    (CA3_4_9I2R4CertificateIndex a) (CA3_4_9I2R4P_sound a)
lemma CA3_4_9I2R4Entropy_sound : CA3_4_9I2R4Entropy.Encloses (Foundation.finiteEntropy CA3_4_9I2R4Value) := by
  exact contains_sound (entropyPair_enclosed CA3_4_9I2R4Value CA3_4_9I2R4Terms CA3_4_9I2R4Terms_sound) (by decide +kernel)
lemma CA3_4_9I2R4Mass_sound : CA3_4_9I2R4Mass.Encloses (∑ a, CA3_4_9I2R4Value a) := by
  exact contains_sound (pairSumBall_sound CA3_4_9I2R4P CA3_4_9I2R4Value CA3_4_9I2R4P_sound) (by decide +kernel)
lemma CA3_4_9I2R4MassTermLog_sound : CA3_4_9I2R4MassTermLog.Encloses (Real.log ((∑ a, CA3_4_9I2R4Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_4_9I2R4Mass_sound) (w := CA3_4_9I2R4MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CA3_4_9I2R4MassTerm_sound : CA3_4_9I2R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_4_9I2R4Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_4_9I2R4Mass_sound) CA3_4_9I2R4MassTermLog_sound) (by decide +kernel)
lemma CA3_4_9I2R4H_sound : CA3_4_9I2R4H.Encloses (homogeneousEntropy CA3_4_9I2R4Value) := by
  exact contains_sound (homogeneous_enclosed CA3_4_9I2R4Value CA3_4_9I2R4MassTerm_sound CA3_4_9I2R4Entropy_sound) (by decide +kernel)
lemma CA3_4_9I2R5Raw_sound (a : PairSlot) :
    (CA3_4_9I2R5Raw a).Encloses (CA3_4_9I2R5Value a) := by
  exact residualBall_sound_on (below (shape 3 4 9)) A3_4_9Law (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_4_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 4 9) (show (shape 3 4 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 5 a
lemma CA3_4_9I2R5Certificates_valid :
    CA3_4_9I2R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA3_4_9I2R5P_check : ∀ a : PairSlot, contains (CA3_4_9I2R5Raw a) (CA3_4_9I2R5P a) = true := by
  decide +kernel
lemma CA3_4_9I2R5P_sound (a : PairSlot) :
    (CA3_4_9I2R5P a).Encloses (CA3_4_9I2R5Value a) :=
  contains_sound (CA3_4_9I2R5Raw_sound a) (CA3_4_9I2R5P_check a)
lemma CA3_4_9I2R5Terms_sound (a : PairSlot) :
    (CA3_4_9I2R5Terms a).Encloses (Foundation.entropyTerm (CA3_4_9I2R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_4_9I2R5Certificates_valid
    (CA3_4_9I2R5CertificateIndex a) (CA3_4_9I2R5P_sound a)
lemma CA3_4_9I2R5Entropy_sound : CA3_4_9I2R5Entropy.Encloses (Foundation.finiteEntropy CA3_4_9I2R5Value) := by
  exact contains_sound (entropyPair_enclosed CA3_4_9I2R5Value CA3_4_9I2R5Terms CA3_4_9I2R5Terms_sound) (by decide +kernel)
lemma CA3_4_9I2R5Mass_sound : CA3_4_9I2R5Mass.Encloses (∑ a, CA3_4_9I2R5Value a) := by
  exact contains_sound (pairSumBall_sound CA3_4_9I2R5P CA3_4_9I2R5Value CA3_4_9I2R5P_sound) (by decide +kernel)
lemma CA3_4_9I2R5MassTermLog_sound : CA3_4_9I2R5MassTermLog.Encloses (Real.log ((∑ a, CA3_4_9I2R5Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_4_9I2R5Mass_sound) (w := CA3_4_9I2R5MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CA3_4_9I2R5MassTerm_sound : CA3_4_9I2R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_4_9I2R5Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_4_9I2R5Mass_sound) CA3_4_9I2R5MassTermLog_sound) (by decide +kernel)
lemma CA3_4_9I2R5H_sound : CA3_4_9I2R5H.Encloses (homogeneousEntropy CA3_4_9I2R5Value) := by
  exact contains_sound (homogeneous_enclosed CA3_4_9I2R5Value CA3_4_9I2R5MassTerm_sound CA3_4_9I2R5Entropy_sound) (by decide +kernel)
lemma CA3_4_9I2R6Raw_sound (a : PairSlot) :
    (CA3_4_9I2R6Raw a).Encloses (CA3_4_9I2R6Value a) := by
  exact residualBall_sound_on (below (shape 3 4 9)) A3_4_9Law (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_4_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 4 9) (show (shape 3 4 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 6 a
lemma CA3_4_9I2R6Certificates_valid :
    CA3_4_9I2R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA3_4_9I2R6P_check : ∀ a : PairSlot, contains (CA3_4_9I2R6Raw a) (CA3_4_9I2R6P a) = true := by
  decide +kernel
lemma CA3_4_9I2R6P_sound (a : PairSlot) :
    (CA3_4_9I2R6P a).Encloses (CA3_4_9I2R6Value a) :=
  contains_sound (CA3_4_9I2R6Raw_sound a) (CA3_4_9I2R6P_check a)
lemma CA3_4_9I2R6Terms_sound (a : PairSlot) :
    (CA3_4_9I2R6Terms a).Encloses (Foundation.entropyTerm (CA3_4_9I2R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_4_9I2R6Certificates_valid
    (CA3_4_9I2R6CertificateIndex a) (CA3_4_9I2R6P_sound a)
lemma CA3_4_9I2R6Entropy_sound : CA3_4_9I2R6Entropy.Encloses (Foundation.finiteEntropy CA3_4_9I2R6Value) := by
  exact contains_sound (entropyPair_enclosed CA3_4_9I2R6Value CA3_4_9I2R6Terms CA3_4_9I2R6Terms_sound) (by decide +kernel)
lemma CA3_4_9I2R6Mass_sound : CA3_4_9I2R6Mass.Encloses (∑ a, CA3_4_9I2R6Value a) := by
  exact contains_sound (pairSumBall_sound CA3_4_9I2R6P CA3_4_9I2R6Value CA3_4_9I2R6P_sound) (by decide +kernel)
lemma CA3_4_9I2R6MassTermLog_sound : CA3_4_9I2R6MassTermLog.Encloses (Real.log ((∑ a, CA3_4_9I2R6Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_4_9I2R6Mass_sound) (w := CA3_4_9I2R6MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CA3_4_9I2R6MassTerm_sound : CA3_4_9I2R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_4_9I2R6Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_4_9I2R6Mass_sound) CA3_4_9I2R6MassTermLog_sound) (by decide +kernel)
lemma CA3_4_9I2R6H_sound : CA3_4_9I2R6H.Encloses (homogeneousEntropy CA3_4_9I2R6Value) := by
  exact contains_sound (homogeneous_enclosed CA3_4_9I2R6Value CA3_4_9I2R6MassTerm_sound CA3_4_9I2R6Entropy_sound) (by decide +kernel)
lemma CA3_4_9I2R8Raw_sound (a : PairSlot) :
    (CA3_4_9I2R8Raw a).Encloses (CA3_4_9I2R8Value a) := by
  exact residualBall_sound_on (below (shape 3 4 9)) A3_4_9Law (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_4_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 4 9) (show (shape 3 4 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 8 a
lemma CA3_4_9I2R8Certificates_valid :
    CA3_4_9I2R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA3_4_9I2R8P_check : ∀ a : PairSlot, contains (CA3_4_9I2R8Raw a) (CA3_4_9I2R8P a) = true := by
  decide +kernel
lemma CA3_4_9I2R8P_sound (a : PairSlot) :
    (CA3_4_9I2R8P a).Encloses (CA3_4_9I2R8Value a) :=
  contains_sound (CA3_4_9I2R8Raw_sound a) (CA3_4_9I2R8P_check a)
lemma CA3_4_9I2R8Terms_sound (a : PairSlot) :
    (CA3_4_9I2R8Terms a).Encloses (Foundation.entropyTerm (CA3_4_9I2R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_4_9I2R8Certificates_valid
    (CA3_4_9I2R8CertificateIndex a) (CA3_4_9I2R8P_sound a)
lemma CA3_4_9I2R8Entropy_sound : CA3_4_9I2R8Entropy.Encloses (Foundation.finiteEntropy CA3_4_9I2R8Value) := by
  exact contains_sound (entropyPair_enclosed CA3_4_9I2R8Value CA3_4_9I2R8Terms CA3_4_9I2R8Terms_sound) (by decide +kernel)
lemma CA3_4_9I2R8Mass_sound : CA3_4_9I2R8Mass.Encloses (∑ a, CA3_4_9I2R8Value a) := by
  exact contains_sound (pairSumBall_sound CA3_4_9I2R8P CA3_4_9I2R8Value CA3_4_9I2R8P_sound) (by decide +kernel)
lemma CA3_4_9I2R8MassTerm_sound : CA3_4_9I2R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_4_9I2R8Value a))) :=
  entropyTerm_zero_ball (CA3_4_9I2R8Mass_sound)
lemma CA3_4_9I2R8H_sound : CA3_4_9I2R8H.Encloses (homogeneousEntropy CA3_4_9I2R8Value) := by
  exact contains_sound (homogeneous_enclosed CA3_4_9I2R8Value CA3_4_9I2R8MassTerm_sound CA3_4_9I2R8Entropy_sound) (by decide +kernel)
lemma CA3_4_9I2R9Raw_sound (a : PairSlot) :
    (CA3_4_9I2R9Raw a).Encloses (CA3_4_9I2R9Value a) := by
  exact residualBall_sound_on (below (shape 3 4 9)) A3_4_9Law (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_4_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 4 9) (show (shape 3 4 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 9 a
lemma CA3_4_9I2R9Certificates_valid :
    CA3_4_9I2R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA3_4_9I2R9P_check : ∀ a : PairSlot, contains (CA3_4_9I2R9Raw a) (CA3_4_9I2R9P a) = true := by
  decide +kernel
lemma CA3_4_9I2R9P_sound (a : PairSlot) :
    (CA3_4_9I2R9P a).Encloses (CA3_4_9I2R9Value a) :=
  contains_sound (CA3_4_9I2R9Raw_sound a) (CA3_4_9I2R9P_check a)
lemma CA3_4_9I2R9Terms_sound (a : PairSlot) :
    (CA3_4_9I2R9Terms a).Encloses (Foundation.entropyTerm (CA3_4_9I2R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_4_9I2R9Certificates_valid
    (CA3_4_9I2R9CertificateIndex a) (CA3_4_9I2R9P_sound a)
lemma CA3_4_9I2R9Entropy_sound : CA3_4_9I2R9Entropy.Encloses (Foundation.finiteEntropy CA3_4_9I2R9Value) := by
  exact contains_sound (entropyPair_enclosed CA3_4_9I2R9Value CA3_4_9I2R9Terms CA3_4_9I2R9Terms_sound) (by decide +kernel)
lemma CA3_4_9I2R9Mass_sound : CA3_4_9I2R9Mass.Encloses (∑ a, CA3_4_9I2R9Value a) := by
  exact contains_sound (pairSumBall_sound CA3_4_9I2R9P CA3_4_9I2R9Value CA3_4_9I2R9P_sound) (by decide +kernel)
lemma CA3_4_9I2R9MassTerm_sound : CA3_4_9I2R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_4_9I2R9Value a))) :=
  entropyTerm_zero_ball (CA3_4_9I2R9Mass_sound)
lemma CA3_4_9I2R9H_sound : CA3_4_9I2R9H.Encloses (homogeneousEntropy CA3_4_9I2R9Value) := by
  exact contains_sound (homogeneous_enclosed CA3_4_9I2R9Value CA3_4_9I2R9MassTerm_sound CA3_4_9I2R9Entropy_sound) (by decide +kernel)
lemma CA3_4_9I2ResidualEntropies_sound (k : Fin 17) :
    (CA3_4_9I2ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 3 4 9)) (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) k)) := by
  fin_cases k
  · exact CA3_4_9I2R0H_sound
  · exact CA3_4_9I2R1H_sound
  · exact CA3_4_9I2R2H_sound
  · exact CA3_4_9I2R3H_sound
  · exact CA3_4_9I2R4H_sound
  · exact CA3_4_9I2R5H_sound
  · exact CA3_4_9I2R6H_sound
  · exact CA3_4_9I2R7H_sound
  · exact CA3_4_9I2R8H_sound
  · exact CA3_4_9I2R9H_sound
  · exact CA3_4_9I2R10H_sound
  · exact CA3_4_9I2R11H_sound
  · exact CA3_4_9I2R12H_sound
  · exact CA3_4_9I2R13H_sound
  · exact CA3_4_9I2R14H_sound
  · exact CA3_4_9I2R15H_sound
  · exact CA3_4_9I2R16H_sound
lemma CA3_4_9I2Singleton_sound : CA3_4_9I2Singleton.Encloses
    (singletonEntropy (below (shape 3 4 9)) (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 3 4 9)) A3_4_9Law (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 2
    CA3_4_9I2Singles (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_4_9Law_sound u) CA3_4_9I2Singles_sound) (by decide +kernel)
lemma CA3_4_9I2Group_sound : CA3_4_9I2Group.Encloses
    (groupedEntropy (below (shape 3 4 9)) (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CA3_4_9I2Singleton_sound
    (finSumBall_sound 17 CA3_4_9I2ResidualEntropies _ CA3_4_9I2ResidualEntropies_sound)) (by decide +kernel)

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
lemma CA3_4_9I2_sound_oai : CA3_4_9I2H.Encloses (stageACapacity (shape 3 4 9) 2) := by
  have hb := contains_sound (Ball.add_sound CA3_4_9I2PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CA3_4_9I2Group_sound)))
    (show contains (.add CA3_4_9I2PairH (.neg (.mul (.exact 2) CA3_4_9I2Group))) CA3_4_9I2H = true by decide +kernel)
  unfold CA3_4_9I2PairValue at hb
  simpa only [stageACapacity, nativeCapacity,
    show (2 : Fin 3) ≠ 0 by decide, ite_false, if_false, sub_eq_add_neg] using hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_4_9I2_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_4_9I2_sound_oai
