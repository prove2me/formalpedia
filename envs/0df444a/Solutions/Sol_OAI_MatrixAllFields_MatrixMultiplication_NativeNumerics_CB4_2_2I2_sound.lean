-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_2_2I2_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:17:41.691315+00:00
-- url     : https://prove2.me/submissions/88658666-0ee4-49ef-9aa7-47469df82fb8

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
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B4_2_2Den_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B4_2_2Raw_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB4_2_2I2Singleton_sound
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

lemma exact_rat_enclosed {q r : ℚ} (h : q = r) : (Ball.exact q).Encloses (r : ℝ) := by
  rw [h]
  exact Ball.exact_sound r

lemma pairSumBall_sound (bs : PairSlot → Ball) (v : PairSlot → ℝ)
    (h : ∀ a, (bs a).Encloses (v a)) :
    (pairSumBall bs).Encloses (∑ a, v a) := by
  exact product_fin6_enclosed _ _ (fun i j => h (i,j))

lemma entropyFin_enclosed (n : ℕ) (p : Fin n → ℝ) (bs : Fin n → Ball)
    (h : ∀ i, (bs i).Encloses (Foundation.entropyTerm (p i))) :
    (finSumBall n bs).Encloses (Foundation.finiteEntropy p) :=
  finSumBall_sound n _ _ h

lemma entropyPair_enclosed (p : PairSlot → ℝ) (bs : PairSlot → Ball)
    (h : ∀ i, (bs i).Encloses (Foundation.entropyTerm (p i))) :
    (pairSumBall bs).Encloses (Foundation.finiteEntropy p) :=
  pairSumBall_sound _ _ h

lemma pairLawBall_sound_on {A : Type*} [Fintype A] (support : List Shape) (s : Shape)
    (bs : Shape → Ball) (p : Shape → ℝ) (bq : Shape → A → Ball) (q : Shape → A → ℝ)
    (hp : ∀ u ∈ support, (bs u).Encloses (p u))
    (hq : ∀ u ∈ support, ∀ a, (bq u a).Encloses (q u a))
    (hcq : ∀ u ∈ support, ∀ a, (bq (complement s u) a).Encloses (q (complement s u) a))
    (ij : A × A) :
    (pairLawBall support s bs bq ij).Encloses (pairLaw support s p q ij) := by
  apply listSumBall_sound
  intro u hu
  exact Ball.mul_sound (Ball.mul_sound (hp u hu) (hq u hu ij.1)) (hcq u hu ij.2)

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
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_LittleB1_3_4
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
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
lemma shapes4_list : shapes 4 = [
  (shape 0 0 4),
  (shape 0 1 3),
  (shape 0 2 2),
  (shape 0 3 1),
  (shape 0 4 0),
  (shape 1 0 3),
  (shape 1 1 2),
  (shape 1 2 1),
  (shape 1 3 0),
  (shape 2 0 2),
  (shape 2 1 1),
  (shape 2 2 0),
  (shape 3 0 1),
  (shape 3 1 0),
  (shape 4 0 0)] := by decide +kernel

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal4_2_2
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
lemma B4_2_2_below : below (shape 4 2 2) = [
  (shape 0 2 2),
  (shape 1 1 2),
  (shape 1 2 1),
  (shape 2 0 2),
  (shape 2 1 1),
  (shape 2 2 0),
  (shape 3 0 1),
  (shape 3 1 0),
  (shape 4 0 0)] := by decide +kernel
lemma B4_2_2Den_positive : 0 < B4_2_2Den.lower := by decide +kernel
lemma B4_2_2Law_check_0_2_2 : contains (.mul (B4_2_2Raw (shape 0 2 2)) (.inv B4_2_2Den)) (B4_2_2Table (shape 0 2 2)) = true := by decide +kernel
lemma B4_2_2Law_check_1_1_2 : contains (.mul (B4_2_2Raw (shape 1 1 2)) (.inv B4_2_2Den)) (B4_2_2Table (shape 1 1 2)) = true := by decide +kernel
lemma B4_2_2Law_check_1_2_1 : contains (.mul (B4_2_2Raw (shape 1 2 1)) (.inv B4_2_2Den)) (B4_2_2Table (shape 1 2 1)) = true := by decide +kernel
lemma B4_2_2Law_check_2_0_2 : contains (.mul (B4_2_2Raw (shape 2 0 2)) (.inv B4_2_2Den)) (B4_2_2Table (shape 2 0 2)) = true := by decide +kernel
lemma B4_2_2Law_check_2_1_1 : contains (.mul (B4_2_2Raw (shape 2 1 1)) (.inv B4_2_2Den)) (B4_2_2Table (shape 2 1 1)) = true := by decide +kernel
lemma B4_2_2Law_check_2_2_0 : contains (.mul (B4_2_2Raw (shape 2 2 0)) (.inv B4_2_2Den)) (B4_2_2Table (shape 2 2 0)) = true := by decide +kernel
lemma B4_2_2Law_check_3_0_1 : contains (.mul (B4_2_2Raw (shape 3 0 1)) (.inv B4_2_2Den)) (B4_2_2Table (shape 3 0 1)) = true := by decide +kernel
lemma B4_2_2Law_check_3_1_0 : contains (.mul (B4_2_2Raw (shape 3 1 0)) (.inv B4_2_2Den)) (B4_2_2Table (shape 3 1 0)) = true := by decide +kernel
lemma B4_2_2Law_check_4_0_0 : contains (.mul (B4_2_2Raw (shape 4 0 0)) (.inv B4_2_2Den)) (B4_2_2Table (shape 4 0 0)) = true := by decide +kernel
lemma B4_2_2Law_check (u : Shape) (hu : u ∈ below (shape 4 2 2)) :
    contains (.mul (B4_2_2Raw u) (.inv B4_2_2Den)) (B4_2_2Table u) = true := by
  rw [B4_2_2_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B4_2_2Law_check_0_2_2
  · exact B4_2_2Law_check_1_1_2
  · exact B4_2_2Law_check_1_2_1
  · exact B4_2_2Law_check_2_0_2
  · exact B4_2_2Law_check_2_1_1
  · exact B4_2_2Law_check_2_2_0
  · exact B4_2_2Law_check_3_0_1
  · exact B4_2_2Law_check_3_1_0
  · exact B4_2_2Law_check_4_0_0
lemma B4_2_2Law_sound (u : Shape) :
    (B4_2_2Law u).Encloses (stageBLaw (shape 4 2 2) u : ℝ) := by
  by_cases hu : u ∈ below (shape 4 2 2)
  · have h := contains_sound (Ball.mul_sound (B4_2_2Raw_sound u hu)
      (Ball.inv_sound B4_2_2Den_sound B4_2_2Den_positive)) (B4_2_2Law_check u hu)
    simpa only [B4_2_2Law, hu, ite_true, if_true, stageBLaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [B4_2_2Law, hu, ite_false, if_false, stageBLaw, splitLaw, Rat.cast_zero]
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
lemma B4_2_2Binary_eq (u : Shape) (hu : u ∈ shapes 4) :
    binaryParameter (shape 4 2 2) u = B4_2_2Binary u := by
  rw [shapes4_list] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

lemma B4_2_2Little_sound (u : Shape) (w : Fin 3) (i : Fin 6) :
    (B4_2_2Little u w i).Encloses (littleLaw (shape 4 2 2) u w i : ℝ) := by
  by_cases hu : u ∈ shapes 4
  · simp only [B4_2_2Little, hu, ite_true, if_true]
    apply exact_rat_enclosed
    simp only [B4_2_2LittleRat, littleLaw, B4_2_2Binary_eq u hu]
  · simp only [B4_2_2Little, hu, ite_false, if_false]
    exact Ball.exact_sound _

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB4_2_2I2
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
lemma CB4_2_2I2PairRaw_sound (a : PairSlot) :
    (CB4_2_2I2PairRaw a).Encloses (CB4_2_2I2PairValue a) := by
  exact pairLawBall_sound_on (below (shape 4 2 2)) (shape 4 2 2) B4_2_2Law (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) (fun u _ => B4_2_2Law_sound u) (fun u _ a => B4_2_2Little_sound u ((stageBPriority (shape 4 2 2)) 2) a) (fun u _ a => B4_2_2Little_sound (complement (shape 4 2 2) u) ((stageBPriority (shape 4 2 2)) 2) a) a
lemma CB4_2_2I2PairCertificates_valid :
    CB4_2_2I2PairCertificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB4_2_2I2PairP_check : ∀ a : PairSlot, contains (CB4_2_2I2PairRaw a) (CB4_2_2I2PairP a) = true := by
  decide +kernel
lemma CB4_2_2I2PairP_sound (a : PairSlot) :
    (CB4_2_2I2PairP a).Encloses (CB4_2_2I2PairValue a) :=
  contains_sound (CB4_2_2I2PairRaw_sound a) (CB4_2_2I2PairP_check a)
lemma CB4_2_2I2PairTerms_sound (a : PairSlot) :
    (CB4_2_2I2PairTerms a).Encloses (Foundation.entropyTerm (CB4_2_2I2PairValue a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_2_2I2PairCertificates_valid
    (CB4_2_2I2PairCertificateIndex a) (CB4_2_2I2PairP_sound a)
lemma CB4_2_2I2PairEntropy_sound : CB4_2_2I2PairEntropy.Encloses (Foundation.finiteEntropy CB4_2_2I2PairValue) := by
  exact contains_sound (entropyPair_enclosed CB4_2_2I2PairValue CB4_2_2I2PairTerms CB4_2_2I2PairTerms_sound) (by decide +kernel)
lemma CB4_2_2I2PairMass_sound : CB4_2_2I2PairMass.Encloses (∑ a, CB4_2_2I2PairValue a) := by
  exact contains_sound (pairSumBall_sound CB4_2_2I2PairP CB4_2_2I2PairValue CB4_2_2I2PairP_sound) (by decide +kernel)
lemma CB4_2_2I2PairMassTermLog_sound : CB4_2_2I2PairMassTermLog.Encloses (Real.log ((∑ a, CB4_2_2I2PairValue a))) := by
  exact checkLog_sound logTwoBall_sound (CB4_2_2I2PairMass_sound) (w := CB4_2_2I2PairMassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CB4_2_2I2PairMassTerm_sound : CB4_2_2I2PairMassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_2_2I2PairValue a))) := by
  exact contains_sound (entropyTerm_ball (CB4_2_2I2PairMass_sound) CB4_2_2I2PairMassTermLog_sound) (by decide +kernel)
lemma CB4_2_2I2PairH_sound : CB4_2_2I2PairH.Encloses (homogeneousEntropy CB4_2_2I2PairValue) := by
  exact contains_sound (homogeneous_enclosed CB4_2_2I2PairValue CB4_2_2I2PairMassTerm_sound CB4_2_2I2PairEntropy_sound) (by decide +kernel)

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
lemma CB4_2_2I2R0Raw_sound (a : Fin 6) :
    (CB4_2_2I2R0Raw a).Encloses (CB4_2_2I2R0Value a) := by
  exact residualBall_sound_on (below (shape 4 2 2)) B4_2_2Law (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) (fun u _ => B4_2_2Law_sound u) (fun u _ a => B4_2_2Little_sound u ((stageBPriority (shape 4 2 2)) 2) a) 0 a
lemma CB4_2_2I2R0Certificates_valid :
    CB4_2_2I2R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB4_2_2I2R0P_check : ∀ a : Fin 6, contains (CB4_2_2I2R0Raw a) (CB4_2_2I2R0P a) = true := by
  decide +kernel
lemma CB4_2_2I2R0P_sound (a : Fin 6) :
    (CB4_2_2I2R0P a).Encloses (CB4_2_2I2R0Value a) :=
  contains_sound (CB4_2_2I2R0Raw_sound a) (CB4_2_2I2R0P_check a)
lemma CB4_2_2I2R0Terms_sound (a : Fin 6) :
    (CB4_2_2I2R0Terms a).Encloses (Foundation.entropyTerm (CB4_2_2I2R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_2_2I2R0Certificates_valid
    (CB4_2_2I2R0CertificateIndex a) (CB4_2_2I2R0P_sound a)
lemma CB4_2_2I2R0Entropy_sound : CB4_2_2I2R0Entropy.Encloses (Foundation.finiteEntropy CB4_2_2I2R0Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_2_2I2R0Value CB4_2_2I2R0Terms CB4_2_2I2R0Terms_sound) (by decide +kernel)
lemma CB4_2_2I2R0Mass_sound : CB4_2_2I2R0Mass.Encloses (∑ a, CB4_2_2I2R0Value a) := by
  exact contains_sound (finSumBall_sound 6 CB4_2_2I2R0P CB4_2_2I2R0Value CB4_2_2I2R0P_sound) (by decide +kernel)
lemma CB4_2_2I2R0MassTermLog_sound : CB4_2_2I2R0MassTermLog.Encloses (Real.log ((∑ a, CB4_2_2I2R0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB4_2_2I2R0Mass_sound) (w := CB4_2_2I2R0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CB4_2_2I2R0MassTerm_sound : CB4_2_2I2R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_2_2I2R0Value a))) := by
  exact contains_sound (entropyTerm_ball (CB4_2_2I2R0Mass_sound) CB4_2_2I2R0MassTermLog_sound) (by decide +kernel)
lemma CB4_2_2I2R0H_sound : CB4_2_2I2R0H.Encloses (homogeneousEntropy CB4_2_2I2R0Value) := by
  exact contains_sound (homogeneous_enclosed CB4_2_2I2R0Value CB4_2_2I2R0MassTerm_sound CB4_2_2I2R0Entropy_sound) (by decide +kernel)
lemma CB4_2_2I2R1Raw_sound (a : Fin 6) :
    (CB4_2_2I2R1Raw a).Encloses (CB4_2_2I2R1Value a) := by
  exact residualBall_sound_on (below (shape 4 2 2)) B4_2_2Law (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) (fun u _ => B4_2_2Law_sound u) (fun u _ a => B4_2_2Little_sound u ((stageBPriority (shape 4 2 2)) 2) a) 1 a
lemma CB4_2_2I2R1Certificates_valid :
    CB4_2_2I2R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB4_2_2I2R1P_check : ∀ a : Fin 6, contains (CB4_2_2I2R1Raw a) (CB4_2_2I2R1P a) = true := by
  decide +kernel
lemma CB4_2_2I2R1P_sound (a : Fin 6) :
    (CB4_2_2I2R1P a).Encloses (CB4_2_2I2R1Value a) :=
  contains_sound (CB4_2_2I2R1Raw_sound a) (CB4_2_2I2R1P_check a)
lemma CB4_2_2I2R1Terms_sound (a : Fin 6) :
    (CB4_2_2I2R1Terms a).Encloses (Foundation.entropyTerm (CB4_2_2I2R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_2_2I2R1Certificates_valid
    (CB4_2_2I2R1CertificateIndex a) (CB4_2_2I2R1P_sound a)
lemma CB4_2_2I2R1Entropy_sound : CB4_2_2I2R1Entropy.Encloses (Foundation.finiteEntropy CB4_2_2I2R1Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_2_2I2R1Value CB4_2_2I2R1Terms CB4_2_2I2R1Terms_sound) (by decide +kernel)
lemma CB4_2_2I2R1Mass_sound : CB4_2_2I2R1Mass.Encloses (∑ a, CB4_2_2I2R1Value a) := by
  exact contains_sound (finSumBall_sound 6 CB4_2_2I2R1P CB4_2_2I2R1Value CB4_2_2I2R1P_sound) (by decide +kernel)
lemma CB4_2_2I2R1MassTermLog_sound : CB4_2_2I2R1MassTermLog.Encloses (Real.log ((∑ a, CB4_2_2I2R1Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB4_2_2I2R1Mass_sound) (w := CB4_2_2I2R1MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CB4_2_2I2R1MassTerm_sound : CB4_2_2I2R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_2_2I2R1Value a))) := by
  exact contains_sound (entropyTerm_ball (CB4_2_2I2R1Mass_sound) CB4_2_2I2R1MassTermLog_sound) (by decide +kernel)
lemma CB4_2_2I2R1H_sound : CB4_2_2I2R1H.Encloses (homogeneousEntropy CB4_2_2I2R1Value) := by
  exact contains_sound (homogeneous_enclosed CB4_2_2I2R1Value CB4_2_2I2R1MassTerm_sound CB4_2_2I2R1Entropy_sound) (by decide +kernel)
lemma CB4_2_2I2R2Raw_sound (a : Fin 6) :
    (CB4_2_2I2R2Raw a).Encloses (CB4_2_2I2R2Value a) := by
  exact residualBall_sound_on (below (shape 4 2 2)) B4_2_2Law (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) (fun u _ => B4_2_2Law_sound u) (fun u _ a => B4_2_2Little_sound u ((stageBPriority (shape 4 2 2)) 2) a) 2 a
lemma CB4_2_2I2R2Certificates_valid :
    CB4_2_2I2R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB4_2_2I2R2P_check : ∀ a : Fin 6, contains (CB4_2_2I2R2Raw a) (CB4_2_2I2R2P a) = true := by
  decide +kernel
lemma CB4_2_2I2R2P_sound (a : Fin 6) :
    (CB4_2_2I2R2P a).Encloses (CB4_2_2I2R2Value a) :=
  contains_sound (CB4_2_2I2R2Raw_sound a) (CB4_2_2I2R2P_check a)
lemma CB4_2_2I2R2Terms_sound (a : Fin 6) :
    (CB4_2_2I2R2Terms a).Encloses (Foundation.entropyTerm (CB4_2_2I2R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_2_2I2R2Certificates_valid
    (CB4_2_2I2R2CertificateIndex a) (CB4_2_2I2R2P_sound a)
lemma CB4_2_2I2R2Entropy_sound : CB4_2_2I2R2Entropy.Encloses (Foundation.finiteEntropy CB4_2_2I2R2Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_2_2I2R2Value CB4_2_2I2R2Terms CB4_2_2I2R2Terms_sound) (by decide +kernel)
lemma CB4_2_2I2R2Mass_sound : CB4_2_2I2R2Mass.Encloses (∑ a, CB4_2_2I2R2Value a) := by
  exact contains_sound (finSumBall_sound 6 CB4_2_2I2R2P CB4_2_2I2R2Value CB4_2_2I2R2P_sound) (by decide +kernel)
lemma CB4_2_2I2R2MassTermLog_sound : CB4_2_2I2R2MassTermLog.Encloses (Real.log ((∑ a, CB4_2_2I2R2Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB4_2_2I2R2Mass_sound) (w := CB4_2_2I2R2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CB4_2_2I2R2MassTerm_sound : CB4_2_2I2R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_2_2I2R2Value a))) := by
  exact contains_sound (entropyTerm_ball (CB4_2_2I2R2Mass_sound) CB4_2_2I2R2MassTermLog_sound) (by decide +kernel)
lemma CB4_2_2I2R2H_sound : CB4_2_2I2R2H.Encloses (homogeneousEntropy CB4_2_2I2R2Value) := by
  exact contains_sound (homogeneous_enclosed CB4_2_2I2R2Value CB4_2_2I2R2MassTerm_sound CB4_2_2I2R2Entropy_sound) (by decide +kernel)
lemma CB4_2_2I2R3Raw_sound (a : Fin 6) :
    (CB4_2_2I2R3Raw a).Encloses (CB4_2_2I2R3Value a) := by
  exact residualBall_sound_on (below (shape 4 2 2)) B4_2_2Law (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) (fun u _ => B4_2_2Law_sound u) (fun u _ a => B4_2_2Little_sound u ((stageBPriority (shape 4 2 2)) 2) a) 3 a
lemma CB4_2_2I2R3Certificates_valid :
    CB4_2_2I2R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB4_2_2I2R3P_check : ∀ a : Fin 6, contains (CB4_2_2I2R3Raw a) (CB4_2_2I2R3P a) = true := by
  decide +kernel
lemma CB4_2_2I2R3P_sound (a : Fin 6) :
    (CB4_2_2I2R3P a).Encloses (CB4_2_2I2R3Value a) :=
  contains_sound (CB4_2_2I2R3Raw_sound a) (CB4_2_2I2R3P_check a)
lemma CB4_2_2I2R3Terms_sound (a : Fin 6) :
    (CB4_2_2I2R3Terms a).Encloses (Foundation.entropyTerm (CB4_2_2I2R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_2_2I2R3Certificates_valid
    (CB4_2_2I2R3CertificateIndex a) (CB4_2_2I2R3P_sound a)
lemma CB4_2_2I2R3Entropy_sound : CB4_2_2I2R3Entropy.Encloses (Foundation.finiteEntropy CB4_2_2I2R3Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_2_2I2R3Value CB4_2_2I2R3Terms CB4_2_2I2R3Terms_sound) (by decide +kernel)
lemma CB4_2_2I2R3Mass_sound : CB4_2_2I2R3Mass.Encloses (∑ a, CB4_2_2I2R3Value a) := by
  exact contains_sound (finSumBall_sound 6 CB4_2_2I2R3P CB4_2_2I2R3Value CB4_2_2I2R3P_sound) (by decide +kernel)
lemma CB4_2_2I2R3MassTerm_sound : CB4_2_2I2R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_2_2I2R3Value a))) :=
  entropyTerm_zero_ball (CB4_2_2I2R3Mass_sound)
lemma CB4_2_2I2R3H_sound : CB4_2_2I2R3H.Encloses (homogeneousEntropy CB4_2_2I2R3Value) := by
  exact contains_sound (homogeneous_enclosed CB4_2_2I2R3Value CB4_2_2I2R3MassTerm_sound CB4_2_2I2R3Entropy_sound) (by decide +kernel)
lemma CB4_2_2I2R4Raw_sound (a : Fin 6) :
    (CB4_2_2I2R4Raw a).Encloses (CB4_2_2I2R4Value a) := by
  exact residualBall_sound_on (below (shape 4 2 2)) B4_2_2Law (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) (fun u _ => B4_2_2Law_sound u) (fun u _ a => B4_2_2Little_sound u ((stageBPriority (shape 4 2 2)) 2) a) 4 a
lemma CB4_2_2I2R4Certificates_valid :
    CB4_2_2I2R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB4_2_2I2R4P_check : ∀ a : Fin 6, contains (CB4_2_2I2R4Raw a) (CB4_2_2I2R4P a) = true := by
  decide +kernel
lemma CB4_2_2I2R4P_sound (a : Fin 6) :
    (CB4_2_2I2R4P a).Encloses (CB4_2_2I2R4Value a) :=
  contains_sound (CB4_2_2I2R4Raw_sound a) (CB4_2_2I2R4P_check a)
lemma CB4_2_2I2R4Terms_sound (a : Fin 6) :
    (CB4_2_2I2R4Terms a).Encloses (Foundation.entropyTerm (CB4_2_2I2R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_2_2I2R4Certificates_valid
    (CB4_2_2I2R4CertificateIndex a) (CB4_2_2I2R4P_sound a)
lemma CB4_2_2I2R4Entropy_sound : CB4_2_2I2R4Entropy.Encloses (Foundation.finiteEntropy CB4_2_2I2R4Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_2_2I2R4Value CB4_2_2I2R4Terms CB4_2_2I2R4Terms_sound) (by decide +kernel)
lemma CB4_2_2I2R4Mass_sound : CB4_2_2I2R4Mass.Encloses (∑ a, CB4_2_2I2R4Value a) := by
  exact contains_sound (finSumBall_sound 6 CB4_2_2I2R4P CB4_2_2I2R4Value CB4_2_2I2R4P_sound) (by decide +kernel)
lemma CB4_2_2I2R4MassTerm_sound : CB4_2_2I2R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_2_2I2R4Value a))) :=
  entropyTerm_zero_ball (CB4_2_2I2R4Mass_sound)
lemma CB4_2_2I2R4H_sound : CB4_2_2I2R4H.Encloses (homogeneousEntropy CB4_2_2I2R4Value) := by
  exact contains_sound (homogeneous_enclosed CB4_2_2I2R4Value CB4_2_2I2R4MassTerm_sound CB4_2_2I2R4Entropy_sound) (by decide +kernel)
lemma CB4_2_2I2R5Raw_sound (a : Fin 6) :
    (CB4_2_2I2R5Raw a).Encloses (CB4_2_2I2R5Value a) := by
  exact residualBall_sound_on (below (shape 4 2 2)) B4_2_2Law (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) (fun u _ => B4_2_2Law_sound u) (fun u _ a => B4_2_2Little_sound u ((stageBPriority (shape 4 2 2)) 2) a) 5 a
lemma CB4_2_2I2R5Certificates_valid :
    CB4_2_2I2R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB4_2_2I2R5P_check : ∀ a : Fin 6, contains (CB4_2_2I2R5Raw a) (CB4_2_2I2R5P a) = true := by
  decide +kernel
lemma CB4_2_2I2R5P_sound (a : Fin 6) :
    (CB4_2_2I2R5P a).Encloses (CB4_2_2I2R5Value a) :=
  contains_sound (CB4_2_2I2R5Raw_sound a) (CB4_2_2I2R5P_check a)
lemma CB4_2_2I2R5Terms_sound (a : Fin 6) :
    (CB4_2_2I2R5Terms a).Encloses (Foundation.entropyTerm (CB4_2_2I2R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_2_2I2R5Certificates_valid
    (CB4_2_2I2R5CertificateIndex a) (CB4_2_2I2R5P_sound a)
lemma CB4_2_2I2R5Entropy_sound : CB4_2_2I2R5Entropy.Encloses (Foundation.finiteEntropy CB4_2_2I2R5Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_2_2I2R5Value CB4_2_2I2R5Terms CB4_2_2I2R5Terms_sound) (by decide +kernel)
lemma CB4_2_2I2R5Mass_sound : CB4_2_2I2R5Mass.Encloses (∑ a, CB4_2_2I2R5Value a) := by
  exact contains_sound (finSumBall_sound 6 CB4_2_2I2R5P CB4_2_2I2R5Value CB4_2_2I2R5P_sound) (by decide +kernel)
lemma CB4_2_2I2R5MassTerm_sound : CB4_2_2I2R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_2_2I2R5Value a))) :=
  entropyTerm_zero_ball (CB4_2_2I2R5Mass_sound)
lemma CB4_2_2I2R5H_sound : CB4_2_2I2R5H.Encloses (homogeneousEntropy CB4_2_2I2R5Value) := by
  exact contains_sound (homogeneous_enclosed CB4_2_2I2R5Value CB4_2_2I2R5MassTerm_sound CB4_2_2I2R5Entropy_sound) (by decide +kernel)
lemma CB4_2_2I2R6Raw_sound (a : Fin 6) :
    (CB4_2_2I2R6Raw a).Encloses (CB4_2_2I2R6Value a) := by
  exact residualBall_sound_on (below (shape 4 2 2)) B4_2_2Law (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) (fun u _ => B4_2_2Law_sound u) (fun u _ a => B4_2_2Little_sound u ((stageBPriority (shape 4 2 2)) 2) a) 6 a
lemma CB4_2_2I2R6Certificates_valid :
    CB4_2_2I2R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB4_2_2I2R6P_check : ∀ a : Fin 6, contains (CB4_2_2I2R6Raw a) (CB4_2_2I2R6P a) = true := by
  decide +kernel
lemma CB4_2_2I2R6P_sound (a : Fin 6) :
    (CB4_2_2I2R6P a).Encloses (CB4_2_2I2R6Value a) :=
  contains_sound (CB4_2_2I2R6Raw_sound a) (CB4_2_2I2R6P_check a)
lemma CB4_2_2I2R6Terms_sound (a : Fin 6) :
    (CB4_2_2I2R6Terms a).Encloses (Foundation.entropyTerm (CB4_2_2I2R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_2_2I2R6Certificates_valid
    (CB4_2_2I2R6CertificateIndex a) (CB4_2_2I2R6P_sound a)
lemma CB4_2_2I2R6Entropy_sound : CB4_2_2I2R6Entropy.Encloses (Foundation.finiteEntropy CB4_2_2I2R6Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_2_2I2R6Value CB4_2_2I2R6Terms CB4_2_2I2R6Terms_sound) (by decide +kernel)
lemma CB4_2_2I2R6Mass_sound : CB4_2_2I2R6Mass.Encloses (∑ a, CB4_2_2I2R6Value a) := by
  exact contains_sound (finSumBall_sound 6 CB4_2_2I2R6P CB4_2_2I2R6Value CB4_2_2I2R6P_sound) (by decide +kernel)
lemma CB4_2_2I2R6MassTerm_sound : CB4_2_2I2R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_2_2I2R6Value a))) :=
  entropyTerm_zero_ball (CB4_2_2I2R6Mass_sound)
lemma CB4_2_2I2R6H_sound : CB4_2_2I2R6H.Encloses (homogeneousEntropy CB4_2_2I2R6Value) := by
  exact contains_sound (homogeneous_enclosed CB4_2_2I2R6Value CB4_2_2I2R6MassTerm_sound CB4_2_2I2R6Entropy_sound) (by decide +kernel)
lemma CB4_2_2I2R7Raw_sound (a : Fin 6) :
    (CB4_2_2I2R7Raw a).Encloses (CB4_2_2I2R7Value a) := by
  exact residualBall_sound_on (below (shape 4 2 2)) B4_2_2Law (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) (fun u _ => B4_2_2Law_sound u) (fun u _ a => B4_2_2Little_sound u ((stageBPriority (shape 4 2 2)) 2) a) 7 a
lemma CB4_2_2I2R7Certificates_valid :
    CB4_2_2I2R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB4_2_2I2R7P_check : ∀ a : Fin 6, contains (CB4_2_2I2R7Raw a) (CB4_2_2I2R7P a) = true := by
  decide +kernel
lemma CB4_2_2I2R7P_sound (a : Fin 6) :
    (CB4_2_2I2R7P a).Encloses (CB4_2_2I2R7Value a) :=
  contains_sound (CB4_2_2I2R7Raw_sound a) (CB4_2_2I2R7P_check a)
lemma CB4_2_2I2R7Terms_sound (a : Fin 6) :
    (CB4_2_2I2R7Terms a).Encloses (Foundation.entropyTerm (CB4_2_2I2R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_2_2I2R7Certificates_valid
    (CB4_2_2I2R7CertificateIndex a) (CB4_2_2I2R7P_sound a)
lemma CB4_2_2I2R7Entropy_sound : CB4_2_2I2R7Entropy.Encloses (Foundation.finiteEntropy CB4_2_2I2R7Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_2_2I2R7Value CB4_2_2I2R7Terms CB4_2_2I2R7Terms_sound) (by decide +kernel)
lemma CB4_2_2I2R7Mass_sound : CB4_2_2I2R7Mass.Encloses (∑ a, CB4_2_2I2R7Value a) := by
  exact contains_sound (finSumBall_sound 6 CB4_2_2I2R7P CB4_2_2I2R7Value CB4_2_2I2R7P_sound) (by decide +kernel)
lemma CB4_2_2I2R7MassTerm_sound : CB4_2_2I2R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_2_2I2R7Value a))) :=
  entropyTerm_zero_ball (CB4_2_2I2R7Mass_sound)
lemma CB4_2_2I2R7H_sound : CB4_2_2I2R7H.Encloses (homogeneousEntropy CB4_2_2I2R7Value) := by
  exact contains_sound (homogeneous_enclosed CB4_2_2I2R7Value CB4_2_2I2R7MassTerm_sound CB4_2_2I2R7Entropy_sound) (by decide +kernel)
lemma CB4_2_2I2R8Raw_sound (a : Fin 6) :
    (CB4_2_2I2R8Raw a).Encloses (CB4_2_2I2R8Value a) := by
  exact residualBall_sound_on (below (shape 4 2 2)) B4_2_2Law (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) (fun u _ => B4_2_2Law_sound u) (fun u _ a => B4_2_2Little_sound u ((stageBPriority (shape 4 2 2)) 2) a) 8 a
lemma CB4_2_2I2R8Certificates_valid :
    CB4_2_2I2R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB4_2_2I2R8P_check : ∀ a : Fin 6, contains (CB4_2_2I2R8Raw a) (CB4_2_2I2R8P a) = true := by
  decide +kernel
lemma CB4_2_2I2R8P_sound (a : Fin 6) :
    (CB4_2_2I2R8P a).Encloses (CB4_2_2I2R8Value a) :=
  contains_sound (CB4_2_2I2R8Raw_sound a) (CB4_2_2I2R8P_check a)
lemma CB4_2_2I2R8Terms_sound (a : Fin 6) :
    (CB4_2_2I2R8Terms a).Encloses (Foundation.entropyTerm (CB4_2_2I2R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_2_2I2R8Certificates_valid
    (CB4_2_2I2R8CertificateIndex a) (CB4_2_2I2R8P_sound a)
lemma CB4_2_2I2R8Entropy_sound : CB4_2_2I2R8Entropy.Encloses (Foundation.finiteEntropy CB4_2_2I2R8Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_2_2I2R8Value CB4_2_2I2R8Terms CB4_2_2I2R8Terms_sound) (by decide +kernel)
lemma CB4_2_2I2R8Mass_sound : CB4_2_2I2R8Mass.Encloses (∑ a, CB4_2_2I2R8Value a) := by
  exact contains_sound (finSumBall_sound 6 CB4_2_2I2R8P CB4_2_2I2R8Value CB4_2_2I2R8P_sound) (by decide +kernel)
lemma CB4_2_2I2R8MassTerm_sound : CB4_2_2I2R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_2_2I2R8Value a))) :=
  entropyTerm_zero_ball (CB4_2_2I2R8Mass_sound)
lemma CB4_2_2I2R8H_sound : CB4_2_2I2R8H.Encloses (homogeneousEntropy CB4_2_2I2R8Value) := by
  exact contains_sound (homogeneous_enclosed CB4_2_2I2R8Value CB4_2_2I2R8MassTerm_sound CB4_2_2I2R8Entropy_sound) (by decide +kernel)
lemma CB4_2_2I2R9Raw_sound (a : Fin 6) :
    (CB4_2_2I2R9Raw a).Encloses (CB4_2_2I2R9Value a) := by
  exact residualBall_sound_on (below (shape 4 2 2)) B4_2_2Law (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) (fun u _ => B4_2_2Law_sound u) (fun u _ a => B4_2_2Little_sound u ((stageBPriority (shape 4 2 2)) 2) a) 9 a
lemma CB4_2_2I2R9Certificates_valid :
    CB4_2_2I2R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB4_2_2I2R9P_check : ∀ a : Fin 6, contains (CB4_2_2I2R9Raw a) (CB4_2_2I2R9P a) = true := by
  decide +kernel
lemma CB4_2_2I2R9P_sound (a : Fin 6) :
    (CB4_2_2I2R9P a).Encloses (CB4_2_2I2R9Value a) :=
  contains_sound (CB4_2_2I2R9Raw_sound a) (CB4_2_2I2R9P_check a)
lemma CB4_2_2I2R9Terms_sound (a : Fin 6) :
    (CB4_2_2I2R9Terms a).Encloses (Foundation.entropyTerm (CB4_2_2I2R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_2_2I2R9Certificates_valid
    (CB4_2_2I2R9CertificateIndex a) (CB4_2_2I2R9P_sound a)
lemma CB4_2_2I2R9Entropy_sound : CB4_2_2I2R9Entropy.Encloses (Foundation.finiteEntropy CB4_2_2I2R9Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_2_2I2R9Value CB4_2_2I2R9Terms CB4_2_2I2R9Terms_sound) (by decide +kernel)
lemma CB4_2_2I2R9Mass_sound : CB4_2_2I2R9Mass.Encloses (∑ a, CB4_2_2I2R9Value a) := by
  exact contains_sound (finSumBall_sound 6 CB4_2_2I2R9P CB4_2_2I2R9Value CB4_2_2I2R9P_sound) (by decide +kernel)
lemma CB4_2_2I2R9MassTerm_sound : CB4_2_2I2R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_2_2I2R9Value a))) :=
  entropyTerm_zero_ball (CB4_2_2I2R9Mass_sound)
lemma CB4_2_2I2R9H_sound : CB4_2_2I2R9H.Encloses (homogeneousEntropy CB4_2_2I2R9Value) := by
  exact contains_sound (homogeneous_enclosed CB4_2_2I2R9Value CB4_2_2I2R9MassTerm_sound CB4_2_2I2R9Entropy_sound) (by decide +kernel)
lemma CB4_2_2I2R10Raw_sound (a : Fin 6) :
    (CB4_2_2I2R10Raw a).Encloses (CB4_2_2I2R10Value a) := by
  exact residualBall_sound_on (below (shape 4 2 2)) B4_2_2Law (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) (fun u _ => B4_2_2Law_sound u) (fun u _ a => B4_2_2Little_sound u ((stageBPriority (shape 4 2 2)) 2) a) 10 a
lemma CB4_2_2I2R10Certificates_valid :
    CB4_2_2I2R10Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB4_2_2I2R10P_check : ∀ a : Fin 6, contains (CB4_2_2I2R10Raw a) (CB4_2_2I2R10P a) = true := by
  decide +kernel
lemma CB4_2_2I2R10P_sound (a : Fin 6) :
    (CB4_2_2I2R10P a).Encloses (CB4_2_2I2R10Value a) :=
  contains_sound (CB4_2_2I2R10Raw_sound a) (CB4_2_2I2R10P_check a)
lemma CB4_2_2I2R10Terms_sound (a : Fin 6) :
    (CB4_2_2I2R10Terms a).Encloses (Foundation.entropyTerm (CB4_2_2I2R10Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_2_2I2R10Certificates_valid
    (CB4_2_2I2R10CertificateIndex a) (CB4_2_2I2R10P_sound a)
lemma CB4_2_2I2R10Entropy_sound : CB4_2_2I2R10Entropy.Encloses (Foundation.finiteEntropy CB4_2_2I2R10Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_2_2I2R10Value CB4_2_2I2R10Terms CB4_2_2I2R10Terms_sound) (by decide +kernel)
lemma CB4_2_2I2R10Mass_sound : CB4_2_2I2R10Mass.Encloses (∑ a, CB4_2_2I2R10Value a) := by
  exact contains_sound (finSumBall_sound 6 CB4_2_2I2R10P CB4_2_2I2R10Value CB4_2_2I2R10P_sound) (by decide +kernel)
lemma CB4_2_2I2R10MassTerm_sound : CB4_2_2I2R10MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_2_2I2R10Value a))) :=
  entropyTerm_zero_ball (CB4_2_2I2R10Mass_sound)
lemma CB4_2_2I2R10H_sound : CB4_2_2I2R10H.Encloses (homogeneousEntropy CB4_2_2I2R10Value) := by
  exact contains_sound (homogeneous_enclosed CB4_2_2I2R10Value CB4_2_2I2R10MassTerm_sound CB4_2_2I2R10Entropy_sound) (by decide +kernel)
lemma CB4_2_2I2R11Raw_sound (a : Fin 6) :
    (CB4_2_2I2R11Raw a).Encloses (CB4_2_2I2R11Value a) := by
  exact residualBall_sound_on (below (shape 4 2 2)) B4_2_2Law (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) (fun u _ => B4_2_2Law_sound u) (fun u _ a => B4_2_2Little_sound u ((stageBPriority (shape 4 2 2)) 2) a) 11 a
lemma CB4_2_2I2R11Certificates_valid :
    CB4_2_2I2R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB4_2_2I2R11P_check : ∀ a : Fin 6, contains (CB4_2_2I2R11Raw a) (CB4_2_2I2R11P a) = true := by
  decide +kernel
lemma CB4_2_2I2R11P_sound (a : Fin 6) :
    (CB4_2_2I2R11P a).Encloses (CB4_2_2I2R11Value a) :=
  contains_sound (CB4_2_2I2R11Raw_sound a) (CB4_2_2I2R11P_check a)
lemma CB4_2_2I2R11Terms_sound (a : Fin 6) :
    (CB4_2_2I2R11Terms a).Encloses (Foundation.entropyTerm (CB4_2_2I2R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_2_2I2R11Certificates_valid
    (CB4_2_2I2R11CertificateIndex a) (CB4_2_2I2R11P_sound a)
lemma CB4_2_2I2R11Entropy_sound : CB4_2_2I2R11Entropy.Encloses (Foundation.finiteEntropy CB4_2_2I2R11Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_2_2I2R11Value CB4_2_2I2R11Terms CB4_2_2I2R11Terms_sound) (by decide +kernel)
lemma CB4_2_2I2R11Mass_sound : CB4_2_2I2R11Mass.Encloses (∑ a, CB4_2_2I2R11Value a) := by
  exact contains_sound (finSumBall_sound 6 CB4_2_2I2R11P CB4_2_2I2R11Value CB4_2_2I2R11P_sound) (by decide +kernel)
lemma CB4_2_2I2R11MassTerm_sound : CB4_2_2I2R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_2_2I2R11Value a))) :=
  entropyTerm_zero_ball (CB4_2_2I2R11Mass_sound)
lemma CB4_2_2I2R11H_sound : CB4_2_2I2R11H.Encloses (homogeneousEntropy CB4_2_2I2R11Value) := by
  exact contains_sound (homogeneous_enclosed CB4_2_2I2R11Value CB4_2_2I2R11MassTerm_sound CB4_2_2I2R11Entropy_sound) (by decide +kernel)
lemma CB4_2_2I2R12Raw_sound (a : Fin 6) :
    (CB4_2_2I2R12Raw a).Encloses (CB4_2_2I2R12Value a) := by
  exact residualBall_sound_on (below (shape 4 2 2)) B4_2_2Law (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) (fun u _ => B4_2_2Law_sound u) (fun u _ a => B4_2_2Little_sound u ((stageBPriority (shape 4 2 2)) 2) a) 12 a
lemma CB4_2_2I2R12Certificates_valid :
    CB4_2_2I2R12Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB4_2_2I2R12P_check : ∀ a : Fin 6, contains (CB4_2_2I2R12Raw a) (CB4_2_2I2R12P a) = true := by
  decide +kernel
lemma CB4_2_2I2R12P_sound (a : Fin 6) :
    (CB4_2_2I2R12P a).Encloses (CB4_2_2I2R12Value a) :=
  contains_sound (CB4_2_2I2R12Raw_sound a) (CB4_2_2I2R12P_check a)
lemma CB4_2_2I2R12Terms_sound (a : Fin 6) :
    (CB4_2_2I2R12Terms a).Encloses (Foundation.entropyTerm (CB4_2_2I2R12Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_2_2I2R12Certificates_valid
    (CB4_2_2I2R12CertificateIndex a) (CB4_2_2I2R12P_sound a)
lemma CB4_2_2I2R12Entropy_sound : CB4_2_2I2R12Entropy.Encloses (Foundation.finiteEntropy CB4_2_2I2R12Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_2_2I2R12Value CB4_2_2I2R12Terms CB4_2_2I2R12Terms_sound) (by decide +kernel)
lemma CB4_2_2I2R12Mass_sound : CB4_2_2I2R12Mass.Encloses (∑ a, CB4_2_2I2R12Value a) := by
  exact contains_sound (finSumBall_sound 6 CB4_2_2I2R12P CB4_2_2I2R12Value CB4_2_2I2R12P_sound) (by decide +kernel)
lemma CB4_2_2I2R12MassTerm_sound : CB4_2_2I2R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_2_2I2R12Value a))) :=
  entropyTerm_zero_ball (CB4_2_2I2R12Mass_sound)
lemma CB4_2_2I2R12H_sound : CB4_2_2I2R12H.Encloses (homogeneousEntropy CB4_2_2I2R12Value) := by
  exact contains_sound (homogeneous_enclosed CB4_2_2I2R12Value CB4_2_2I2R12MassTerm_sound CB4_2_2I2R12Entropy_sound) (by decide +kernel)
lemma CB4_2_2I2R13Raw_sound (a : Fin 6) :
    (CB4_2_2I2R13Raw a).Encloses (CB4_2_2I2R13Value a) := by
  exact residualBall_sound_on (below (shape 4 2 2)) B4_2_2Law (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) (fun u _ => B4_2_2Law_sound u) (fun u _ a => B4_2_2Little_sound u ((stageBPriority (shape 4 2 2)) 2) a) 13 a
lemma CB4_2_2I2R13Certificates_valid :
    CB4_2_2I2R13Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB4_2_2I2R13P_check : ∀ a : Fin 6, contains (CB4_2_2I2R13Raw a) (CB4_2_2I2R13P a) = true := by
  decide +kernel
lemma CB4_2_2I2R13P_sound (a : Fin 6) :
    (CB4_2_2I2R13P a).Encloses (CB4_2_2I2R13Value a) :=
  contains_sound (CB4_2_2I2R13Raw_sound a) (CB4_2_2I2R13P_check a)
lemma CB4_2_2I2R13Terms_sound (a : Fin 6) :
    (CB4_2_2I2R13Terms a).Encloses (Foundation.entropyTerm (CB4_2_2I2R13Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_2_2I2R13Certificates_valid
    (CB4_2_2I2R13CertificateIndex a) (CB4_2_2I2R13P_sound a)
lemma CB4_2_2I2R13Entropy_sound : CB4_2_2I2R13Entropy.Encloses (Foundation.finiteEntropy CB4_2_2I2R13Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_2_2I2R13Value CB4_2_2I2R13Terms CB4_2_2I2R13Terms_sound) (by decide +kernel)
lemma CB4_2_2I2R13Mass_sound : CB4_2_2I2R13Mass.Encloses (∑ a, CB4_2_2I2R13Value a) := by
  exact contains_sound (finSumBall_sound 6 CB4_2_2I2R13P CB4_2_2I2R13Value CB4_2_2I2R13P_sound) (by decide +kernel)
lemma CB4_2_2I2R13MassTerm_sound : CB4_2_2I2R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_2_2I2R13Value a))) :=
  entropyTerm_zero_ball (CB4_2_2I2R13Mass_sound)
lemma CB4_2_2I2R13H_sound : CB4_2_2I2R13H.Encloses (homogeneousEntropy CB4_2_2I2R13Value) := by
  exact contains_sound (homogeneous_enclosed CB4_2_2I2R13Value CB4_2_2I2R13MassTerm_sound CB4_2_2I2R13Entropy_sound) (by decide +kernel)
lemma CB4_2_2I2R14Raw_sound (a : Fin 6) :
    (CB4_2_2I2R14Raw a).Encloses (CB4_2_2I2R14Value a) := by
  exact residualBall_sound_on (below (shape 4 2 2)) B4_2_2Law (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) (fun u _ => B4_2_2Law_sound u) (fun u _ a => B4_2_2Little_sound u ((stageBPriority (shape 4 2 2)) 2) a) 14 a
lemma CB4_2_2I2R14Certificates_valid :
    CB4_2_2I2R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB4_2_2I2R14P_check : ∀ a : Fin 6, contains (CB4_2_2I2R14Raw a) (CB4_2_2I2R14P a) = true := by
  decide +kernel
lemma CB4_2_2I2R14P_sound (a : Fin 6) :
    (CB4_2_2I2R14P a).Encloses (CB4_2_2I2R14Value a) :=
  contains_sound (CB4_2_2I2R14Raw_sound a) (CB4_2_2I2R14P_check a)
lemma CB4_2_2I2R14Terms_sound (a : Fin 6) :
    (CB4_2_2I2R14Terms a).Encloses (Foundation.entropyTerm (CB4_2_2I2R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_2_2I2R14Certificates_valid
    (CB4_2_2I2R14CertificateIndex a) (CB4_2_2I2R14P_sound a)
lemma CB4_2_2I2R14Entropy_sound : CB4_2_2I2R14Entropy.Encloses (Foundation.finiteEntropy CB4_2_2I2R14Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_2_2I2R14Value CB4_2_2I2R14Terms CB4_2_2I2R14Terms_sound) (by decide +kernel)
lemma CB4_2_2I2R14Mass_sound : CB4_2_2I2R14Mass.Encloses (∑ a, CB4_2_2I2R14Value a) := by
  exact contains_sound (finSumBall_sound 6 CB4_2_2I2R14P CB4_2_2I2R14Value CB4_2_2I2R14P_sound) (by decide +kernel)
lemma CB4_2_2I2R14MassTerm_sound : CB4_2_2I2R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_2_2I2R14Value a))) :=
  entropyTerm_zero_ball (CB4_2_2I2R14Mass_sound)
lemma CB4_2_2I2R14H_sound : CB4_2_2I2R14H.Encloses (homogeneousEntropy CB4_2_2I2R14Value) := by
  exact contains_sound (homogeneous_enclosed CB4_2_2I2R14Value CB4_2_2I2R14MassTerm_sound CB4_2_2I2R14Entropy_sound) (by decide +kernel)
lemma CB4_2_2I2R15Raw_sound (a : Fin 6) :
    (CB4_2_2I2R15Raw a).Encloses (CB4_2_2I2R15Value a) := by
  exact residualBall_sound_on (below (shape 4 2 2)) B4_2_2Law (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) (fun u _ => B4_2_2Law_sound u) (fun u _ a => B4_2_2Little_sound u ((stageBPriority (shape 4 2 2)) 2) a) 15 a
lemma CB4_2_2I2R15Certificates_valid :
    CB4_2_2I2R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB4_2_2I2R15P_check : ∀ a : Fin 6, contains (CB4_2_2I2R15Raw a) (CB4_2_2I2R15P a) = true := by
  decide +kernel
lemma CB4_2_2I2R15P_sound (a : Fin 6) :
    (CB4_2_2I2R15P a).Encloses (CB4_2_2I2R15Value a) :=
  contains_sound (CB4_2_2I2R15Raw_sound a) (CB4_2_2I2R15P_check a)
lemma CB4_2_2I2R15Terms_sound (a : Fin 6) :
    (CB4_2_2I2R15Terms a).Encloses (Foundation.entropyTerm (CB4_2_2I2R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_2_2I2R15Certificates_valid
    (CB4_2_2I2R15CertificateIndex a) (CB4_2_2I2R15P_sound a)
lemma CB4_2_2I2R15Entropy_sound : CB4_2_2I2R15Entropy.Encloses (Foundation.finiteEntropy CB4_2_2I2R15Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_2_2I2R15Value CB4_2_2I2R15Terms CB4_2_2I2R15Terms_sound) (by decide +kernel)
lemma CB4_2_2I2R15Mass_sound : CB4_2_2I2R15Mass.Encloses (∑ a, CB4_2_2I2R15Value a) := by
  exact contains_sound (finSumBall_sound 6 CB4_2_2I2R15P CB4_2_2I2R15Value CB4_2_2I2R15P_sound) (by decide +kernel)
lemma CB4_2_2I2R15MassTerm_sound : CB4_2_2I2R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_2_2I2R15Value a))) :=
  entropyTerm_zero_ball (CB4_2_2I2R15Mass_sound)
lemma CB4_2_2I2R15H_sound : CB4_2_2I2R15H.Encloses (homogeneousEntropy CB4_2_2I2R15Value) := by
  exact contains_sound (homogeneous_enclosed CB4_2_2I2R15Value CB4_2_2I2R15MassTerm_sound CB4_2_2I2R15Entropy_sound) (by decide +kernel)
lemma CB4_2_2I2R16Raw_sound (a : Fin 6) :
    (CB4_2_2I2R16Raw a).Encloses (CB4_2_2I2R16Value a) := by
  exact residualBall_sound_on (below (shape 4 2 2)) B4_2_2Law (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u => B4_2_2Little u ((stageBPriority (shape 4 2 2)) 2)) (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) (fun u _ => B4_2_2Law_sound u) (fun u _ a => B4_2_2Little_sound u ((stageBPriority (shape 4 2 2)) 2) a) 16 a
lemma CB4_2_2I2R16Certificates_valid :
    CB4_2_2I2R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB4_2_2I2R16P_check : ∀ a : Fin 6, contains (CB4_2_2I2R16Raw a) (CB4_2_2I2R16P a) = true := by
  decide +kernel
lemma CB4_2_2I2R16P_sound (a : Fin 6) :
    (CB4_2_2I2R16P a).Encloses (CB4_2_2I2R16Value a) :=
  contains_sound (CB4_2_2I2R16Raw_sound a) (CB4_2_2I2R16P_check a)
lemma CB4_2_2I2R16Terms_sound (a : Fin 6) :
    (CB4_2_2I2R16Terms a).Encloses (Foundation.entropyTerm (CB4_2_2I2R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_2_2I2R16Certificates_valid
    (CB4_2_2I2R16CertificateIndex a) (CB4_2_2I2R16P_sound a)
lemma CB4_2_2I2R16Entropy_sound : CB4_2_2I2R16Entropy.Encloses (Foundation.finiteEntropy CB4_2_2I2R16Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_2_2I2R16Value CB4_2_2I2R16Terms CB4_2_2I2R16Terms_sound) (by decide +kernel)
lemma CB4_2_2I2R16Mass_sound : CB4_2_2I2R16Mass.Encloses (∑ a, CB4_2_2I2R16Value a) := by
  exact contains_sound (finSumBall_sound 6 CB4_2_2I2R16P CB4_2_2I2R16Value CB4_2_2I2R16P_sound) (by decide +kernel)
lemma CB4_2_2I2R16MassTerm_sound : CB4_2_2I2R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_2_2I2R16Value a))) :=
  entropyTerm_zero_ball (CB4_2_2I2R16Mass_sound)
lemma CB4_2_2I2R16H_sound : CB4_2_2I2R16H.Encloses (homogeneousEntropy CB4_2_2I2R16Value) := by
  exact contains_sound (homogeneous_enclosed CB4_2_2I2R16Value CB4_2_2I2R16MassTerm_sound CB4_2_2I2R16Entropy_sound) (by decide +kernel)
lemma CB4_2_2I2ResidualEntropies_sound (k : Fin 17) :
    (CB4_2_2I2ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ)) k)) := by
  fin_cases k
  · exact CB4_2_2I2R0H_sound
  · exact CB4_2_2I2R1H_sound
  · exact CB4_2_2I2R2H_sound
  · exact CB4_2_2I2R3H_sound
  · exact CB4_2_2I2R4H_sound
  · exact CB4_2_2I2R5H_sound
  · exact CB4_2_2I2R6H_sound
  · exact CB4_2_2I2R7H_sound
  · exact CB4_2_2I2R8H_sound
  · exact CB4_2_2I2R9H_sound
  · exact CB4_2_2I2R10H_sound
  · exact CB4_2_2I2R11H_sound
  · exact CB4_2_2I2R12H_sound
  · exact CB4_2_2I2R13H_sound
  · exact CB4_2_2I2R14H_sound
  · exact CB4_2_2I2R15H_sound
  · exact CB4_2_2I2R16H_sound
lemma CB4_2_2I2Group_sound : CB4_2_2I2Group.Encloses
    (groupedEntropy (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (stageBPriority (shape 4 2 2)) 2 (fun u a => (littleLaw (shape 4 2 2) u ((stageBPriority (shape 4 2 2)) 2) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CB4_2_2I2Singleton_sound
    (finSumBall_sound 17 CB4_2_2I2ResidualEntropies _ CB4_2_2I2ResidualEntropies_sound)) (by decide +kernel)

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
lemma CB4_2_2I2_sound_oai : CB4_2_2I2H.Encloses (stageBCapacity (shape 4 2 2) 2) := by
  have hb := contains_sound (Ball.add_sound CB4_2_2I2PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CB4_2_2I2Group_sound)))
    (show contains (.add CB4_2_2I2PairH (.neg (.mul (.exact 2) CB4_2_2I2Group))) CB4_2_2I2H = true by decide +kernel)
  simp only [stageBCapacity, nativeCapacity,
    show (2 : Fin 3) ≠ 0 by decide, ite_false, if_false, sub_eq_add_neg]
  exact hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_2_2I2_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_2_2I2_sound_oai
