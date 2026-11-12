-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_3_1I1_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:17:42.954252+00:00
-- url     : https://prove2.me/submissions/8601f58d-09a5-48e9-a2a6-653fe967800c

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
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B4_3_1Den_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B4_3_1Raw_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB4_3_1I1R10H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB4_3_1I1Singleton_sound
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
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal4_3_1
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
lemma B4_3_1_below : below (shape 4 3 1) = [
  (shape 0 3 1),
  (shape 1 2 1),
  (shape 1 3 0),
  (shape 2 1 1),
  (shape 2 2 0),
  (shape 3 0 1),
  (shape 3 1 0),
  (shape 4 0 0)] := by decide +kernel
lemma B4_3_1Den_positive : 0 < B4_3_1Den.lower := by decide +kernel
lemma B4_3_1Law_check_0_3_1 : contains (.mul (B4_3_1Raw (shape 0 3 1)) (.inv B4_3_1Den)) (B4_3_1Table (shape 0 3 1)) = true := by decide +kernel
lemma B4_3_1Law_check_1_2_1 : contains (.mul (B4_3_1Raw (shape 1 2 1)) (.inv B4_3_1Den)) (B4_3_1Table (shape 1 2 1)) = true := by decide +kernel
lemma B4_3_1Law_check_1_3_0 : contains (.mul (B4_3_1Raw (shape 1 3 0)) (.inv B4_3_1Den)) (B4_3_1Table (shape 1 3 0)) = true := by decide +kernel
lemma B4_3_1Law_check_2_1_1 : contains (.mul (B4_3_1Raw (shape 2 1 1)) (.inv B4_3_1Den)) (B4_3_1Table (shape 2 1 1)) = true := by decide +kernel
lemma B4_3_1Law_check_2_2_0 : contains (.mul (B4_3_1Raw (shape 2 2 0)) (.inv B4_3_1Den)) (B4_3_1Table (shape 2 2 0)) = true := by decide +kernel
lemma B4_3_1Law_check_3_0_1 : contains (.mul (B4_3_1Raw (shape 3 0 1)) (.inv B4_3_1Den)) (B4_3_1Table (shape 3 0 1)) = true := by decide +kernel
lemma B4_3_1Law_check_3_1_0 : contains (.mul (B4_3_1Raw (shape 3 1 0)) (.inv B4_3_1Den)) (B4_3_1Table (shape 3 1 0)) = true := by decide +kernel
lemma B4_3_1Law_check_4_0_0 : contains (.mul (B4_3_1Raw (shape 4 0 0)) (.inv B4_3_1Den)) (B4_3_1Table (shape 4 0 0)) = true := by decide +kernel
lemma B4_3_1Law_check (u : Shape) (hu : u ∈ below (shape 4 3 1)) :
    contains (.mul (B4_3_1Raw u) (.inv B4_3_1Den)) (B4_3_1Table u) = true := by
  rw [B4_3_1_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B4_3_1Law_check_0_3_1
  · exact B4_3_1Law_check_1_2_1
  · exact B4_3_1Law_check_1_3_0
  · exact B4_3_1Law_check_2_1_1
  · exact B4_3_1Law_check_2_2_0
  · exact B4_3_1Law_check_3_0_1
  · exact B4_3_1Law_check_3_1_0
  · exact B4_3_1Law_check_4_0_0
lemma B4_3_1Law_sound (u : Shape) :
    (B4_3_1Law u).Encloses (stageBLaw (shape 4 3 1) u : ℝ) := by
  by_cases hu : u ∈ below (shape 4 3 1)
  · have h := contains_sound (Ball.mul_sound (B4_3_1Raw_sound u hu)
      (Ball.inv_sound B4_3_1Den_sound B4_3_1Den_positive)) (B4_3_1Law_check u hu)
    simpa only [B4_3_1Law, hu, ite_true, if_true, stageBLaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [B4_3_1Law, hu, ite_false, if_false, stageBLaw, splitLaw, Rat.cast_zero]
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
lemma B4_3_1Binary_eq (u : Shape) (hu : u ∈ shapes 4) :
    binaryParameter (shape 4 3 1) u = B4_3_1Binary u := by
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

lemma B4_3_1Little_sound (u : Shape) (w : Fin 3) (i : Fin 6) :
    (B4_3_1Little u w i).Encloses (littleLaw (shape 4 3 1) u w i : ℝ) := by
  by_cases hu : u ∈ shapes 4
  · simp only [B4_3_1Little, hu, ite_true, if_true]
    apply exact_rat_enclosed
    simp only [B4_3_1LittleRat, littleLaw, B4_3_1Binary_eq u hu]
  · simp only [B4_3_1Little, hu, ite_false, if_false]
    exact Ball.exact_sound _

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB4_3_1I1
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
lemma CB4_3_1I1PairRaw_sound (a : PairSlot) :
    (CB4_3_1I1PairRaw a).Encloses (CB4_3_1I1PairValue a) := by
  exact pairLawBall_sound_on (below (shape 4 3 1)) (shape 4 3 1) B4_3_1Law (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (fun u => B4_3_1Little u ((stageBPriority (shape 4 3 1)) 1)) (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 1) a : ℝ)) (fun u _ => B4_3_1Law_sound u) (fun u _ a => B4_3_1Little_sound u ((stageBPriority (shape 4 3 1)) 1) a) (fun u _ a => B4_3_1Little_sound (complement (shape 4 3 1) u) ((stageBPriority (shape 4 3 1)) 1) a) a
lemma CB4_3_1I1PairCertificates_valid :
    CB4_3_1I1PairCertificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB4_3_1I1PairP_check : ∀ a : PairSlot, contains (CB4_3_1I1PairRaw a) (CB4_3_1I1PairP a) = true := by
  decide +kernel
lemma CB4_3_1I1PairP_sound (a : PairSlot) :
    (CB4_3_1I1PairP a).Encloses (CB4_3_1I1PairValue a) :=
  contains_sound (CB4_3_1I1PairRaw_sound a) (CB4_3_1I1PairP_check a)
lemma CB4_3_1I1PairTerms_sound (a : PairSlot) :
    (CB4_3_1I1PairTerms a).Encloses (Foundation.entropyTerm (CB4_3_1I1PairValue a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_3_1I1PairCertificates_valid
    (CB4_3_1I1PairCertificateIndex a) (CB4_3_1I1PairP_sound a)
lemma CB4_3_1I1PairEntropy_sound : CB4_3_1I1PairEntropy.Encloses (Foundation.finiteEntropy CB4_3_1I1PairValue) := by
  exact contains_sound (entropyPair_enclosed CB4_3_1I1PairValue CB4_3_1I1PairTerms CB4_3_1I1PairTerms_sound) (by decide +kernel)
lemma CB4_3_1I1PairMass_sound : CB4_3_1I1PairMass.Encloses (∑ a, CB4_3_1I1PairValue a) := by
  exact contains_sound (pairSumBall_sound CB4_3_1I1PairP CB4_3_1I1PairValue CB4_3_1I1PairP_sound) (by decide +kernel)
lemma CB4_3_1I1PairMassTermLog_sound : CB4_3_1I1PairMassTermLog.Encloses (Real.log ((∑ a, CB4_3_1I1PairValue a))) := by
  exact checkLog_sound logTwoBall_sound (CB4_3_1I1PairMass_sound) (w := CB4_3_1I1PairMassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CB4_3_1I1PairMassTerm_sound : CB4_3_1I1PairMassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_3_1I1PairValue a))) := by
  exact contains_sound (entropyTerm_ball (CB4_3_1I1PairMass_sound) CB4_3_1I1PairMassTermLog_sound) (by decide +kernel)
lemma CB4_3_1I1PairH_sound : CB4_3_1I1PairH.Encloses (homogeneousEntropy CB4_3_1I1PairValue) := by
  exact contains_sound (homogeneous_enclosed CB4_3_1I1PairValue CB4_3_1I1PairMassTerm_sound CB4_3_1I1PairEntropy_sound) (by decide +kernel)

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
lemma CB4_3_1I1R0Raw_sound (a : Fin 6) :
    (CB4_3_1I1R0Raw a).Encloses (CB4_3_1I1R0Value a) := by
  exact residualBall_sound_on (below (shape 4 3 1)) B4_3_1Law (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (stageBPriority (shape 4 3 1)) 1 (fun u => B4_3_1Little u ((stageBPriority (shape 4 3 1)) 1)) (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 1) a : ℝ)) (fun u _ => B4_3_1Law_sound u) (fun u _ a => B4_3_1Little_sound u ((stageBPriority (shape 4 3 1)) 1) a) 0 a
lemma CB4_3_1I1R0Certificates_valid :
    CB4_3_1I1R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB4_3_1I1R0P_check : ∀ a : Fin 6, contains (CB4_3_1I1R0Raw a) (CB4_3_1I1R0P a) = true := by
  decide +kernel
lemma CB4_3_1I1R0P_sound (a : Fin 6) :
    (CB4_3_1I1R0P a).Encloses (CB4_3_1I1R0Value a) :=
  contains_sound (CB4_3_1I1R0Raw_sound a) (CB4_3_1I1R0P_check a)
lemma CB4_3_1I1R0Terms_sound (a : Fin 6) :
    (CB4_3_1I1R0Terms a).Encloses (Foundation.entropyTerm (CB4_3_1I1R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_3_1I1R0Certificates_valid
    (CB4_3_1I1R0CertificateIndex a) (CB4_3_1I1R0P_sound a)
lemma CB4_3_1I1R0Entropy_sound : CB4_3_1I1R0Entropy.Encloses (Foundation.finiteEntropy CB4_3_1I1R0Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_3_1I1R0Value CB4_3_1I1R0Terms CB4_3_1I1R0Terms_sound) (by decide +kernel)
lemma CB4_3_1I1R0Mass_sound : CB4_3_1I1R0Mass.Encloses (∑ a, CB4_3_1I1R0Value a) := by
  exact contains_sound (finSumBall_sound 6 CB4_3_1I1R0P CB4_3_1I1R0Value CB4_3_1I1R0P_sound) (by decide +kernel)
lemma CB4_3_1I1R0MassTermLog_sound : CB4_3_1I1R0MassTermLog.Encloses (Real.log ((∑ a, CB4_3_1I1R0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB4_3_1I1R0Mass_sound) (w := CB4_3_1I1R0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CB4_3_1I1R0MassTerm_sound : CB4_3_1I1R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_3_1I1R0Value a))) := by
  exact contains_sound (entropyTerm_ball (CB4_3_1I1R0Mass_sound) CB4_3_1I1R0MassTermLog_sound) (by decide +kernel)
lemma CB4_3_1I1R0H_sound : CB4_3_1I1R0H.Encloses (homogeneousEntropy CB4_3_1I1R0Value) := by
  exact contains_sound (homogeneous_enclosed CB4_3_1I1R0Value CB4_3_1I1R0MassTerm_sound CB4_3_1I1R0Entropy_sound) (by decide +kernel)
lemma CB4_3_1I1R1Raw_sound (a : Fin 6) :
    (CB4_3_1I1R1Raw a).Encloses (CB4_3_1I1R1Value a) := by
  exact residualBall_sound_on (below (shape 4 3 1)) B4_3_1Law (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (stageBPriority (shape 4 3 1)) 1 (fun u => B4_3_1Little u ((stageBPriority (shape 4 3 1)) 1)) (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 1) a : ℝ)) (fun u _ => B4_3_1Law_sound u) (fun u _ a => B4_3_1Little_sound u ((stageBPriority (shape 4 3 1)) 1) a) 1 a
lemma CB4_3_1I1R1Certificates_valid :
    CB4_3_1I1R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB4_3_1I1R1P_check : ∀ a : Fin 6, contains (CB4_3_1I1R1Raw a) (CB4_3_1I1R1P a) = true := by
  decide +kernel
lemma CB4_3_1I1R1P_sound (a : Fin 6) :
    (CB4_3_1I1R1P a).Encloses (CB4_3_1I1R1Value a) :=
  contains_sound (CB4_3_1I1R1Raw_sound a) (CB4_3_1I1R1P_check a)
lemma CB4_3_1I1R1Terms_sound (a : Fin 6) :
    (CB4_3_1I1R1Terms a).Encloses (Foundation.entropyTerm (CB4_3_1I1R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_3_1I1R1Certificates_valid
    (CB4_3_1I1R1CertificateIndex a) (CB4_3_1I1R1P_sound a)
lemma CB4_3_1I1R1Entropy_sound : CB4_3_1I1R1Entropy.Encloses (Foundation.finiteEntropy CB4_3_1I1R1Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_3_1I1R1Value CB4_3_1I1R1Terms CB4_3_1I1R1Terms_sound) (by decide +kernel)
lemma CB4_3_1I1R1Mass_sound : CB4_3_1I1R1Mass.Encloses (∑ a, CB4_3_1I1R1Value a) := by
  exact contains_sound (finSumBall_sound 6 CB4_3_1I1R1P CB4_3_1I1R1Value CB4_3_1I1R1P_sound) (by decide +kernel)
lemma CB4_3_1I1R1MassTermLog_sound : CB4_3_1I1R1MassTermLog.Encloses (Real.log ((∑ a, CB4_3_1I1R1Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB4_3_1I1R1Mass_sound) (w := CB4_3_1I1R1MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CB4_3_1I1R1MassTerm_sound : CB4_3_1I1R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_3_1I1R1Value a))) := by
  exact contains_sound (entropyTerm_ball (CB4_3_1I1R1Mass_sound) CB4_3_1I1R1MassTermLog_sound) (by decide +kernel)
lemma CB4_3_1I1R1H_sound : CB4_3_1I1R1H.Encloses (homogeneousEntropy CB4_3_1I1R1Value) := by
  exact contains_sound (homogeneous_enclosed CB4_3_1I1R1Value CB4_3_1I1R1MassTerm_sound CB4_3_1I1R1Entropy_sound) (by decide +kernel)
lemma CB4_3_1I1R2Raw_sound (a : Fin 6) :
    (CB4_3_1I1R2Raw a).Encloses (CB4_3_1I1R2Value a) := by
  exact residualBall_sound_on (below (shape 4 3 1)) B4_3_1Law (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (stageBPriority (shape 4 3 1)) 1 (fun u => B4_3_1Little u ((stageBPriority (shape 4 3 1)) 1)) (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 1) a : ℝ)) (fun u _ => B4_3_1Law_sound u) (fun u _ a => B4_3_1Little_sound u ((stageBPriority (shape 4 3 1)) 1) a) 2 a
lemma CB4_3_1I1R2Certificates_valid :
    CB4_3_1I1R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB4_3_1I1R2P_check : ∀ a : Fin 6, contains (CB4_3_1I1R2Raw a) (CB4_3_1I1R2P a) = true := by
  decide +kernel
lemma CB4_3_1I1R2P_sound (a : Fin 6) :
    (CB4_3_1I1R2P a).Encloses (CB4_3_1I1R2Value a) :=
  contains_sound (CB4_3_1I1R2Raw_sound a) (CB4_3_1I1R2P_check a)
lemma CB4_3_1I1R2Terms_sound (a : Fin 6) :
    (CB4_3_1I1R2Terms a).Encloses (Foundation.entropyTerm (CB4_3_1I1R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_3_1I1R2Certificates_valid
    (CB4_3_1I1R2CertificateIndex a) (CB4_3_1I1R2P_sound a)
lemma CB4_3_1I1R2Entropy_sound : CB4_3_1I1R2Entropy.Encloses (Foundation.finiteEntropy CB4_3_1I1R2Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_3_1I1R2Value CB4_3_1I1R2Terms CB4_3_1I1R2Terms_sound) (by decide +kernel)
lemma CB4_3_1I1R2Mass_sound : CB4_3_1I1R2Mass.Encloses (∑ a, CB4_3_1I1R2Value a) := by
  exact contains_sound (finSumBall_sound 6 CB4_3_1I1R2P CB4_3_1I1R2Value CB4_3_1I1R2P_sound) (by decide +kernel)
lemma CB4_3_1I1R2MassTermLog_sound : CB4_3_1I1R2MassTermLog.Encloses (Real.log ((∑ a, CB4_3_1I1R2Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB4_3_1I1R2Mass_sound) (w := CB4_3_1I1R2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CB4_3_1I1R2MassTerm_sound : CB4_3_1I1R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_3_1I1R2Value a))) := by
  exact contains_sound (entropyTerm_ball (CB4_3_1I1R2Mass_sound) CB4_3_1I1R2MassTermLog_sound) (by decide +kernel)
lemma CB4_3_1I1R2H_sound : CB4_3_1I1R2H.Encloses (homogeneousEntropy CB4_3_1I1R2Value) := by
  exact contains_sound (homogeneous_enclosed CB4_3_1I1R2Value CB4_3_1I1R2MassTerm_sound CB4_3_1I1R2Entropy_sound) (by decide +kernel)
lemma CB4_3_1I1R3Raw_sound (a : Fin 6) :
    (CB4_3_1I1R3Raw a).Encloses (CB4_3_1I1R3Value a) := by
  exact residualBall_sound_on (below (shape 4 3 1)) B4_3_1Law (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (stageBPriority (shape 4 3 1)) 1 (fun u => B4_3_1Little u ((stageBPriority (shape 4 3 1)) 1)) (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 1) a : ℝ)) (fun u _ => B4_3_1Law_sound u) (fun u _ a => B4_3_1Little_sound u ((stageBPriority (shape 4 3 1)) 1) a) 3 a
lemma CB4_3_1I1R3Certificates_valid :
    CB4_3_1I1R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB4_3_1I1R3P_check : ∀ a : Fin 6, contains (CB4_3_1I1R3Raw a) (CB4_3_1I1R3P a) = true := by
  decide +kernel
lemma CB4_3_1I1R3P_sound (a : Fin 6) :
    (CB4_3_1I1R3P a).Encloses (CB4_3_1I1R3Value a) :=
  contains_sound (CB4_3_1I1R3Raw_sound a) (CB4_3_1I1R3P_check a)
lemma CB4_3_1I1R3Terms_sound (a : Fin 6) :
    (CB4_3_1I1R3Terms a).Encloses (Foundation.entropyTerm (CB4_3_1I1R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_3_1I1R3Certificates_valid
    (CB4_3_1I1R3CertificateIndex a) (CB4_3_1I1R3P_sound a)
lemma CB4_3_1I1R3Entropy_sound : CB4_3_1I1R3Entropy.Encloses (Foundation.finiteEntropy CB4_3_1I1R3Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_3_1I1R3Value CB4_3_1I1R3Terms CB4_3_1I1R3Terms_sound) (by decide +kernel)
lemma CB4_3_1I1R3Mass_sound : CB4_3_1I1R3Mass.Encloses (∑ a, CB4_3_1I1R3Value a) := by
  exact contains_sound (finSumBall_sound 6 CB4_3_1I1R3P CB4_3_1I1R3Value CB4_3_1I1R3P_sound) (by decide +kernel)
lemma CB4_3_1I1R3MassTermLog_sound : CB4_3_1I1R3MassTermLog.Encloses (Real.log ((∑ a, CB4_3_1I1R3Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB4_3_1I1R3Mass_sound) (w := CB4_3_1I1R3MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CB4_3_1I1R3MassTerm_sound : CB4_3_1I1R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_3_1I1R3Value a))) := by
  exact contains_sound (entropyTerm_ball (CB4_3_1I1R3Mass_sound) CB4_3_1I1R3MassTermLog_sound) (by decide +kernel)
lemma CB4_3_1I1R3H_sound : CB4_3_1I1R3H.Encloses (homogeneousEntropy CB4_3_1I1R3Value) := by
  exact contains_sound (homogeneous_enclosed CB4_3_1I1R3Value CB4_3_1I1R3MassTerm_sound CB4_3_1I1R3Entropy_sound) (by decide +kernel)
lemma CB4_3_1I1R4Raw_sound (a : Fin 6) :
    (CB4_3_1I1R4Raw a).Encloses (CB4_3_1I1R4Value a) := by
  exact residualBall_sound_on (below (shape 4 3 1)) B4_3_1Law (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (stageBPriority (shape 4 3 1)) 1 (fun u => B4_3_1Little u ((stageBPriority (shape 4 3 1)) 1)) (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 1) a : ℝ)) (fun u _ => B4_3_1Law_sound u) (fun u _ a => B4_3_1Little_sound u ((stageBPriority (shape 4 3 1)) 1) a) 4 a
lemma CB4_3_1I1R4Certificates_valid :
    CB4_3_1I1R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB4_3_1I1R4P_check : ∀ a : Fin 6, contains (CB4_3_1I1R4Raw a) (CB4_3_1I1R4P a) = true := by
  decide +kernel
lemma CB4_3_1I1R4P_sound (a : Fin 6) :
    (CB4_3_1I1R4P a).Encloses (CB4_3_1I1R4Value a) :=
  contains_sound (CB4_3_1I1R4Raw_sound a) (CB4_3_1I1R4P_check a)
lemma CB4_3_1I1R4Terms_sound (a : Fin 6) :
    (CB4_3_1I1R4Terms a).Encloses (Foundation.entropyTerm (CB4_3_1I1R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_3_1I1R4Certificates_valid
    (CB4_3_1I1R4CertificateIndex a) (CB4_3_1I1R4P_sound a)
lemma CB4_3_1I1R4Entropy_sound : CB4_3_1I1R4Entropy.Encloses (Foundation.finiteEntropy CB4_3_1I1R4Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_3_1I1R4Value CB4_3_1I1R4Terms CB4_3_1I1R4Terms_sound) (by decide +kernel)
lemma CB4_3_1I1R4Mass_sound : CB4_3_1I1R4Mass.Encloses (∑ a, CB4_3_1I1R4Value a) := by
  exact contains_sound (finSumBall_sound 6 CB4_3_1I1R4P CB4_3_1I1R4Value CB4_3_1I1R4P_sound) (by decide +kernel)
lemma CB4_3_1I1R4MassTerm_sound : CB4_3_1I1R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_3_1I1R4Value a))) :=
  entropyTerm_zero_ball (CB4_3_1I1R4Mass_sound)
lemma CB4_3_1I1R4H_sound : CB4_3_1I1R4H.Encloses (homogeneousEntropy CB4_3_1I1R4Value) := by
  exact contains_sound (homogeneous_enclosed CB4_3_1I1R4Value CB4_3_1I1R4MassTerm_sound CB4_3_1I1R4Entropy_sound) (by decide +kernel)
lemma CB4_3_1I1R5Raw_sound (a : Fin 6) :
    (CB4_3_1I1R5Raw a).Encloses (CB4_3_1I1R5Value a) := by
  exact residualBall_sound_on (below (shape 4 3 1)) B4_3_1Law (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (stageBPriority (shape 4 3 1)) 1 (fun u => B4_3_1Little u ((stageBPriority (shape 4 3 1)) 1)) (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 1) a : ℝ)) (fun u _ => B4_3_1Law_sound u) (fun u _ a => B4_3_1Little_sound u ((stageBPriority (shape 4 3 1)) 1) a) 5 a
lemma CB4_3_1I1R5Certificates_valid :
    CB4_3_1I1R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB4_3_1I1R5P_check : ∀ a : Fin 6, contains (CB4_3_1I1R5Raw a) (CB4_3_1I1R5P a) = true := by
  decide +kernel
lemma CB4_3_1I1R5P_sound (a : Fin 6) :
    (CB4_3_1I1R5P a).Encloses (CB4_3_1I1R5Value a) :=
  contains_sound (CB4_3_1I1R5Raw_sound a) (CB4_3_1I1R5P_check a)
lemma CB4_3_1I1R5Terms_sound (a : Fin 6) :
    (CB4_3_1I1R5Terms a).Encloses (Foundation.entropyTerm (CB4_3_1I1R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_3_1I1R5Certificates_valid
    (CB4_3_1I1R5CertificateIndex a) (CB4_3_1I1R5P_sound a)
lemma CB4_3_1I1R5Entropy_sound : CB4_3_1I1R5Entropy.Encloses (Foundation.finiteEntropy CB4_3_1I1R5Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_3_1I1R5Value CB4_3_1I1R5Terms CB4_3_1I1R5Terms_sound) (by decide +kernel)
lemma CB4_3_1I1R5Mass_sound : CB4_3_1I1R5Mass.Encloses (∑ a, CB4_3_1I1R5Value a) := by
  exact contains_sound (finSumBall_sound 6 CB4_3_1I1R5P CB4_3_1I1R5Value CB4_3_1I1R5P_sound) (by decide +kernel)
lemma CB4_3_1I1R5MassTerm_sound : CB4_3_1I1R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_3_1I1R5Value a))) :=
  entropyTerm_zero_ball (CB4_3_1I1R5Mass_sound)
lemma CB4_3_1I1R5H_sound : CB4_3_1I1R5H.Encloses (homogeneousEntropy CB4_3_1I1R5Value) := by
  exact contains_sound (homogeneous_enclosed CB4_3_1I1R5Value CB4_3_1I1R5MassTerm_sound CB4_3_1I1R5Entropy_sound) (by decide +kernel)
lemma CB4_3_1I1R6Raw_sound (a : Fin 6) :
    (CB4_3_1I1R6Raw a).Encloses (CB4_3_1I1R6Value a) := by
  exact residualBall_sound_on (below (shape 4 3 1)) B4_3_1Law (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (stageBPriority (shape 4 3 1)) 1 (fun u => B4_3_1Little u ((stageBPriority (shape 4 3 1)) 1)) (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 1) a : ℝ)) (fun u _ => B4_3_1Law_sound u) (fun u _ a => B4_3_1Little_sound u ((stageBPriority (shape 4 3 1)) 1) a) 6 a
lemma CB4_3_1I1R6Certificates_valid :
    CB4_3_1I1R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB4_3_1I1R6P_check : ∀ a : Fin 6, contains (CB4_3_1I1R6Raw a) (CB4_3_1I1R6P a) = true := by
  decide +kernel
lemma CB4_3_1I1R6P_sound (a : Fin 6) :
    (CB4_3_1I1R6P a).Encloses (CB4_3_1I1R6Value a) :=
  contains_sound (CB4_3_1I1R6Raw_sound a) (CB4_3_1I1R6P_check a)
lemma CB4_3_1I1R6Terms_sound (a : Fin 6) :
    (CB4_3_1I1R6Terms a).Encloses (Foundation.entropyTerm (CB4_3_1I1R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_3_1I1R6Certificates_valid
    (CB4_3_1I1R6CertificateIndex a) (CB4_3_1I1R6P_sound a)
lemma CB4_3_1I1R6Entropy_sound : CB4_3_1I1R6Entropy.Encloses (Foundation.finiteEntropy CB4_3_1I1R6Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_3_1I1R6Value CB4_3_1I1R6Terms CB4_3_1I1R6Terms_sound) (by decide +kernel)
lemma CB4_3_1I1R6Mass_sound : CB4_3_1I1R6Mass.Encloses (∑ a, CB4_3_1I1R6Value a) := by
  exact contains_sound (finSumBall_sound 6 CB4_3_1I1R6P CB4_3_1I1R6Value CB4_3_1I1R6P_sound) (by decide +kernel)
lemma CB4_3_1I1R6MassTerm_sound : CB4_3_1I1R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_3_1I1R6Value a))) :=
  entropyTerm_zero_ball (CB4_3_1I1R6Mass_sound)
lemma CB4_3_1I1R6H_sound : CB4_3_1I1R6H.Encloses (homogeneousEntropy CB4_3_1I1R6Value) := by
  exact contains_sound (homogeneous_enclosed CB4_3_1I1R6Value CB4_3_1I1R6MassTerm_sound CB4_3_1I1R6Entropy_sound) (by decide +kernel)
lemma CB4_3_1I1R7Raw_sound (a : Fin 6) :
    (CB4_3_1I1R7Raw a).Encloses (CB4_3_1I1R7Value a) := by
  exact residualBall_sound_on (below (shape 4 3 1)) B4_3_1Law (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (stageBPriority (shape 4 3 1)) 1 (fun u => B4_3_1Little u ((stageBPriority (shape 4 3 1)) 1)) (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 1) a : ℝ)) (fun u _ => B4_3_1Law_sound u) (fun u _ a => B4_3_1Little_sound u ((stageBPriority (shape 4 3 1)) 1) a) 7 a
lemma CB4_3_1I1R7Certificates_valid :
    CB4_3_1I1R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB4_3_1I1R7P_check : ∀ a : Fin 6, contains (CB4_3_1I1R7Raw a) (CB4_3_1I1R7P a) = true := by
  decide +kernel
lemma CB4_3_1I1R7P_sound (a : Fin 6) :
    (CB4_3_1I1R7P a).Encloses (CB4_3_1I1R7Value a) :=
  contains_sound (CB4_3_1I1R7Raw_sound a) (CB4_3_1I1R7P_check a)
lemma CB4_3_1I1R7Terms_sound (a : Fin 6) :
    (CB4_3_1I1R7Terms a).Encloses (Foundation.entropyTerm (CB4_3_1I1R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_3_1I1R7Certificates_valid
    (CB4_3_1I1R7CertificateIndex a) (CB4_3_1I1R7P_sound a)
lemma CB4_3_1I1R7Entropy_sound : CB4_3_1I1R7Entropy.Encloses (Foundation.finiteEntropy CB4_3_1I1R7Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_3_1I1R7Value CB4_3_1I1R7Terms CB4_3_1I1R7Terms_sound) (by decide +kernel)
lemma CB4_3_1I1R7Mass_sound : CB4_3_1I1R7Mass.Encloses (∑ a, CB4_3_1I1R7Value a) := by
  exact contains_sound (finSumBall_sound 6 CB4_3_1I1R7P CB4_3_1I1R7Value CB4_3_1I1R7P_sound) (by decide +kernel)
lemma CB4_3_1I1R7MassTerm_sound : CB4_3_1I1R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_3_1I1R7Value a))) :=
  entropyTerm_zero_ball (CB4_3_1I1R7Mass_sound)
lemma CB4_3_1I1R7H_sound : CB4_3_1I1R7H.Encloses (homogeneousEntropy CB4_3_1I1R7Value) := by
  exact contains_sound (homogeneous_enclosed CB4_3_1I1R7Value CB4_3_1I1R7MassTerm_sound CB4_3_1I1R7Entropy_sound) (by decide +kernel)
lemma CB4_3_1I1R8Raw_sound (a : Fin 6) :
    (CB4_3_1I1R8Raw a).Encloses (CB4_3_1I1R8Value a) := by
  exact residualBall_sound_on (below (shape 4 3 1)) B4_3_1Law (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (stageBPriority (shape 4 3 1)) 1 (fun u => B4_3_1Little u ((stageBPriority (shape 4 3 1)) 1)) (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 1) a : ℝ)) (fun u _ => B4_3_1Law_sound u) (fun u _ a => B4_3_1Little_sound u ((stageBPriority (shape 4 3 1)) 1) a) 8 a
lemma CB4_3_1I1R8Certificates_valid :
    CB4_3_1I1R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB4_3_1I1R8P_check : ∀ a : Fin 6, contains (CB4_3_1I1R8Raw a) (CB4_3_1I1R8P a) = true := by
  decide +kernel
lemma CB4_3_1I1R8P_sound (a : Fin 6) :
    (CB4_3_1I1R8P a).Encloses (CB4_3_1I1R8Value a) :=
  contains_sound (CB4_3_1I1R8Raw_sound a) (CB4_3_1I1R8P_check a)
lemma CB4_3_1I1R8Terms_sound (a : Fin 6) :
    (CB4_3_1I1R8Terms a).Encloses (Foundation.entropyTerm (CB4_3_1I1R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_3_1I1R8Certificates_valid
    (CB4_3_1I1R8CertificateIndex a) (CB4_3_1I1R8P_sound a)
lemma CB4_3_1I1R8Entropy_sound : CB4_3_1I1R8Entropy.Encloses (Foundation.finiteEntropy CB4_3_1I1R8Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_3_1I1R8Value CB4_3_1I1R8Terms CB4_3_1I1R8Terms_sound) (by decide +kernel)
lemma CB4_3_1I1R8Mass_sound : CB4_3_1I1R8Mass.Encloses (∑ a, CB4_3_1I1R8Value a) := by
  exact contains_sound (finSumBall_sound 6 CB4_3_1I1R8P CB4_3_1I1R8Value CB4_3_1I1R8P_sound) (by decide +kernel)
lemma CB4_3_1I1R8MassTerm_sound : CB4_3_1I1R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_3_1I1R8Value a))) :=
  entropyTerm_zero_ball (CB4_3_1I1R8Mass_sound)
lemma CB4_3_1I1R8H_sound : CB4_3_1I1R8H.Encloses (homogeneousEntropy CB4_3_1I1R8Value) := by
  exact contains_sound (homogeneous_enclosed CB4_3_1I1R8Value CB4_3_1I1R8MassTerm_sound CB4_3_1I1R8Entropy_sound) (by decide +kernel)
lemma CB4_3_1I1R9Raw_sound (a : Fin 6) :
    (CB4_3_1I1R9Raw a).Encloses (CB4_3_1I1R9Value a) := by
  exact residualBall_sound_on (below (shape 4 3 1)) B4_3_1Law (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (stageBPriority (shape 4 3 1)) 1 (fun u => B4_3_1Little u ((stageBPriority (shape 4 3 1)) 1)) (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 1) a : ℝ)) (fun u _ => B4_3_1Law_sound u) (fun u _ a => B4_3_1Little_sound u ((stageBPriority (shape 4 3 1)) 1) a) 9 a
lemma CB4_3_1I1R9Certificates_valid :
    CB4_3_1I1R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB4_3_1I1R9P_check : ∀ a : Fin 6, contains (CB4_3_1I1R9Raw a) (CB4_3_1I1R9P a) = true := by
  decide +kernel
lemma CB4_3_1I1R9P_sound (a : Fin 6) :
    (CB4_3_1I1R9P a).Encloses (CB4_3_1I1R9Value a) :=
  contains_sound (CB4_3_1I1R9Raw_sound a) (CB4_3_1I1R9P_check a)
lemma CB4_3_1I1R9Terms_sound (a : Fin 6) :
    (CB4_3_1I1R9Terms a).Encloses (Foundation.entropyTerm (CB4_3_1I1R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_3_1I1R9Certificates_valid
    (CB4_3_1I1R9CertificateIndex a) (CB4_3_1I1R9P_sound a)
lemma CB4_3_1I1R9Entropy_sound : CB4_3_1I1R9Entropy.Encloses (Foundation.finiteEntropy CB4_3_1I1R9Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_3_1I1R9Value CB4_3_1I1R9Terms CB4_3_1I1R9Terms_sound) (by decide +kernel)
lemma CB4_3_1I1R9Mass_sound : CB4_3_1I1R9Mass.Encloses (∑ a, CB4_3_1I1R9Value a) := by
  exact contains_sound (finSumBall_sound 6 CB4_3_1I1R9P CB4_3_1I1R9Value CB4_3_1I1R9P_sound) (by decide +kernel)
lemma CB4_3_1I1R9MassTerm_sound : CB4_3_1I1R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_3_1I1R9Value a))) :=
  entropyTerm_zero_ball (CB4_3_1I1R9Mass_sound)
lemma CB4_3_1I1R9H_sound : CB4_3_1I1R9H.Encloses (homogeneousEntropy CB4_3_1I1R9Value) := by
  exact contains_sound (homogeneous_enclosed CB4_3_1I1R9Value CB4_3_1I1R9MassTerm_sound CB4_3_1I1R9Entropy_sound) (by decide +kernel)
lemma CB4_3_1I1R11Raw_sound (a : Fin 6) :
    (CB4_3_1I1R11Raw a).Encloses (CB4_3_1I1R11Value a) := by
  exact residualBall_sound_on (below (shape 4 3 1)) B4_3_1Law (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (stageBPriority (shape 4 3 1)) 1 (fun u => B4_3_1Little u ((stageBPriority (shape 4 3 1)) 1)) (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 1) a : ℝ)) (fun u _ => B4_3_1Law_sound u) (fun u _ a => B4_3_1Little_sound u ((stageBPriority (shape 4 3 1)) 1) a) 11 a
lemma CB4_3_1I1R11Certificates_valid :
    CB4_3_1I1R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB4_3_1I1R11P_check : ∀ a : Fin 6, contains (CB4_3_1I1R11Raw a) (CB4_3_1I1R11P a) = true := by
  decide +kernel
lemma CB4_3_1I1R11P_sound (a : Fin 6) :
    (CB4_3_1I1R11P a).Encloses (CB4_3_1I1R11Value a) :=
  contains_sound (CB4_3_1I1R11Raw_sound a) (CB4_3_1I1R11P_check a)
lemma CB4_3_1I1R11Terms_sound (a : Fin 6) :
    (CB4_3_1I1R11Terms a).Encloses (Foundation.entropyTerm (CB4_3_1I1R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_3_1I1R11Certificates_valid
    (CB4_3_1I1R11CertificateIndex a) (CB4_3_1I1R11P_sound a)
lemma CB4_3_1I1R11Entropy_sound : CB4_3_1I1R11Entropy.Encloses (Foundation.finiteEntropy CB4_3_1I1R11Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_3_1I1R11Value CB4_3_1I1R11Terms CB4_3_1I1R11Terms_sound) (by decide +kernel)
lemma CB4_3_1I1R11Mass_sound : CB4_3_1I1R11Mass.Encloses (∑ a, CB4_3_1I1R11Value a) := by
  exact contains_sound (finSumBall_sound 6 CB4_3_1I1R11P CB4_3_1I1R11Value CB4_3_1I1R11P_sound) (by decide +kernel)
lemma CB4_3_1I1R11MassTerm_sound : CB4_3_1I1R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_3_1I1R11Value a))) :=
  entropyTerm_zero_ball (CB4_3_1I1R11Mass_sound)
lemma CB4_3_1I1R11H_sound : CB4_3_1I1R11H.Encloses (homogeneousEntropy CB4_3_1I1R11Value) := by
  exact contains_sound (homogeneous_enclosed CB4_3_1I1R11Value CB4_3_1I1R11MassTerm_sound CB4_3_1I1R11Entropy_sound) (by decide +kernel)
lemma CB4_3_1I1R12Raw_sound (a : Fin 6) :
    (CB4_3_1I1R12Raw a).Encloses (CB4_3_1I1R12Value a) := by
  exact residualBall_sound_on (below (shape 4 3 1)) B4_3_1Law (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (stageBPriority (shape 4 3 1)) 1 (fun u => B4_3_1Little u ((stageBPriority (shape 4 3 1)) 1)) (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 1) a : ℝ)) (fun u _ => B4_3_1Law_sound u) (fun u _ a => B4_3_1Little_sound u ((stageBPriority (shape 4 3 1)) 1) a) 12 a
lemma CB4_3_1I1R12Certificates_valid :
    CB4_3_1I1R12Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB4_3_1I1R12P_check : ∀ a : Fin 6, contains (CB4_3_1I1R12Raw a) (CB4_3_1I1R12P a) = true := by
  decide +kernel
lemma CB4_3_1I1R12P_sound (a : Fin 6) :
    (CB4_3_1I1R12P a).Encloses (CB4_3_1I1R12Value a) :=
  contains_sound (CB4_3_1I1R12Raw_sound a) (CB4_3_1I1R12P_check a)
lemma CB4_3_1I1R12Terms_sound (a : Fin 6) :
    (CB4_3_1I1R12Terms a).Encloses (Foundation.entropyTerm (CB4_3_1I1R12Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_3_1I1R12Certificates_valid
    (CB4_3_1I1R12CertificateIndex a) (CB4_3_1I1R12P_sound a)
lemma CB4_3_1I1R12Entropy_sound : CB4_3_1I1R12Entropy.Encloses (Foundation.finiteEntropy CB4_3_1I1R12Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_3_1I1R12Value CB4_3_1I1R12Terms CB4_3_1I1R12Terms_sound) (by decide +kernel)
lemma CB4_3_1I1R12Mass_sound : CB4_3_1I1R12Mass.Encloses (∑ a, CB4_3_1I1R12Value a) := by
  exact contains_sound (finSumBall_sound 6 CB4_3_1I1R12P CB4_3_1I1R12Value CB4_3_1I1R12P_sound) (by decide +kernel)
lemma CB4_3_1I1R12MassTerm_sound : CB4_3_1I1R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_3_1I1R12Value a))) :=
  entropyTerm_zero_ball (CB4_3_1I1R12Mass_sound)
lemma CB4_3_1I1R12H_sound : CB4_3_1I1R12H.Encloses (homogeneousEntropy CB4_3_1I1R12Value) := by
  exact contains_sound (homogeneous_enclosed CB4_3_1I1R12Value CB4_3_1I1R12MassTerm_sound CB4_3_1I1R12Entropy_sound) (by decide +kernel)
lemma CB4_3_1I1R13Raw_sound (a : Fin 6) :
    (CB4_3_1I1R13Raw a).Encloses (CB4_3_1I1R13Value a) := by
  exact residualBall_sound_on (below (shape 4 3 1)) B4_3_1Law (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (stageBPriority (shape 4 3 1)) 1 (fun u => B4_3_1Little u ((stageBPriority (shape 4 3 1)) 1)) (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 1) a : ℝ)) (fun u _ => B4_3_1Law_sound u) (fun u _ a => B4_3_1Little_sound u ((stageBPriority (shape 4 3 1)) 1) a) 13 a
lemma CB4_3_1I1R13Certificates_valid :
    CB4_3_1I1R13Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB4_3_1I1R13P_check : ∀ a : Fin 6, contains (CB4_3_1I1R13Raw a) (CB4_3_1I1R13P a) = true := by
  decide +kernel
lemma CB4_3_1I1R13P_sound (a : Fin 6) :
    (CB4_3_1I1R13P a).Encloses (CB4_3_1I1R13Value a) :=
  contains_sound (CB4_3_1I1R13Raw_sound a) (CB4_3_1I1R13P_check a)
lemma CB4_3_1I1R13Terms_sound (a : Fin 6) :
    (CB4_3_1I1R13Terms a).Encloses (Foundation.entropyTerm (CB4_3_1I1R13Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_3_1I1R13Certificates_valid
    (CB4_3_1I1R13CertificateIndex a) (CB4_3_1I1R13P_sound a)
lemma CB4_3_1I1R13Entropy_sound : CB4_3_1I1R13Entropy.Encloses (Foundation.finiteEntropy CB4_3_1I1R13Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_3_1I1R13Value CB4_3_1I1R13Terms CB4_3_1I1R13Terms_sound) (by decide +kernel)
lemma CB4_3_1I1R13Mass_sound : CB4_3_1I1R13Mass.Encloses (∑ a, CB4_3_1I1R13Value a) := by
  exact contains_sound (finSumBall_sound 6 CB4_3_1I1R13P CB4_3_1I1R13Value CB4_3_1I1R13P_sound) (by decide +kernel)
lemma CB4_3_1I1R13MassTerm_sound : CB4_3_1I1R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_3_1I1R13Value a))) :=
  entropyTerm_zero_ball (CB4_3_1I1R13Mass_sound)
lemma CB4_3_1I1R13H_sound : CB4_3_1I1R13H.Encloses (homogeneousEntropy CB4_3_1I1R13Value) := by
  exact contains_sound (homogeneous_enclosed CB4_3_1I1R13Value CB4_3_1I1R13MassTerm_sound CB4_3_1I1R13Entropy_sound) (by decide +kernel)
lemma CB4_3_1I1R14Raw_sound (a : Fin 6) :
    (CB4_3_1I1R14Raw a).Encloses (CB4_3_1I1R14Value a) := by
  exact residualBall_sound_on (below (shape 4 3 1)) B4_3_1Law (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (stageBPriority (shape 4 3 1)) 1 (fun u => B4_3_1Little u ((stageBPriority (shape 4 3 1)) 1)) (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 1) a : ℝ)) (fun u _ => B4_3_1Law_sound u) (fun u _ a => B4_3_1Little_sound u ((stageBPriority (shape 4 3 1)) 1) a) 14 a
lemma CB4_3_1I1R14Certificates_valid :
    CB4_3_1I1R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB4_3_1I1R14P_check : ∀ a : Fin 6, contains (CB4_3_1I1R14Raw a) (CB4_3_1I1R14P a) = true := by
  decide +kernel
lemma CB4_3_1I1R14P_sound (a : Fin 6) :
    (CB4_3_1I1R14P a).Encloses (CB4_3_1I1R14Value a) :=
  contains_sound (CB4_3_1I1R14Raw_sound a) (CB4_3_1I1R14P_check a)
lemma CB4_3_1I1R14Terms_sound (a : Fin 6) :
    (CB4_3_1I1R14Terms a).Encloses (Foundation.entropyTerm (CB4_3_1I1R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_3_1I1R14Certificates_valid
    (CB4_3_1I1R14CertificateIndex a) (CB4_3_1I1R14P_sound a)
lemma CB4_3_1I1R14Entropy_sound : CB4_3_1I1R14Entropy.Encloses (Foundation.finiteEntropy CB4_3_1I1R14Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_3_1I1R14Value CB4_3_1I1R14Terms CB4_3_1I1R14Terms_sound) (by decide +kernel)
lemma CB4_3_1I1R14Mass_sound : CB4_3_1I1R14Mass.Encloses (∑ a, CB4_3_1I1R14Value a) := by
  exact contains_sound (finSumBall_sound 6 CB4_3_1I1R14P CB4_3_1I1R14Value CB4_3_1I1R14P_sound) (by decide +kernel)
lemma CB4_3_1I1R14MassTerm_sound : CB4_3_1I1R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_3_1I1R14Value a))) :=
  entropyTerm_zero_ball (CB4_3_1I1R14Mass_sound)
lemma CB4_3_1I1R14H_sound : CB4_3_1I1R14H.Encloses (homogeneousEntropy CB4_3_1I1R14Value) := by
  exact contains_sound (homogeneous_enclosed CB4_3_1I1R14Value CB4_3_1I1R14MassTerm_sound CB4_3_1I1R14Entropy_sound) (by decide +kernel)
lemma CB4_3_1I1R15Raw_sound (a : Fin 6) :
    (CB4_3_1I1R15Raw a).Encloses (CB4_3_1I1R15Value a) := by
  exact residualBall_sound_on (below (shape 4 3 1)) B4_3_1Law (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (stageBPriority (shape 4 3 1)) 1 (fun u => B4_3_1Little u ((stageBPriority (shape 4 3 1)) 1)) (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 1) a : ℝ)) (fun u _ => B4_3_1Law_sound u) (fun u _ a => B4_3_1Little_sound u ((stageBPriority (shape 4 3 1)) 1) a) 15 a
lemma CB4_3_1I1R15Certificates_valid :
    CB4_3_1I1R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB4_3_1I1R15P_check : ∀ a : Fin 6, contains (CB4_3_1I1R15Raw a) (CB4_3_1I1R15P a) = true := by
  decide +kernel
lemma CB4_3_1I1R15P_sound (a : Fin 6) :
    (CB4_3_1I1R15P a).Encloses (CB4_3_1I1R15Value a) :=
  contains_sound (CB4_3_1I1R15Raw_sound a) (CB4_3_1I1R15P_check a)
lemma CB4_3_1I1R15Terms_sound (a : Fin 6) :
    (CB4_3_1I1R15Terms a).Encloses (Foundation.entropyTerm (CB4_3_1I1R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_3_1I1R15Certificates_valid
    (CB4_3_1I1R15CertificateIndex a) (CB4_3_1I1R15P_sound a)
lemma CB4_3_1I1R15Entropy_sound : CB4_3_1I1R15Entropy.Encloses (Foundation.finiteEntropy CB4_3_1I1R15Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_3_1I1R15Value CB4_3_1I1R15Terms CB4_3_1I1R15Terms_sound) (by decide +kernel)
lemma CB4_3_1I1R15Mass_sound : CB4_3_1I1R15Mass.Encloses (∑ a, CB4_3_1I1R15Value a) := by
  exact contains_sound (finSumBall_sound 6 CB4_3_1I1R15P CB4_3_1I1R15Value CB4_3_1I1R15P_sound) (by decide +kernel)
lemma CB4_3_1I1R15MassTerm_sound : CB4_3_1I1R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_3_1I1R15Value a))) :=
  entropyTerm_zero_ball (CB4_3_1I1R15Mass_sound)
lemma CB4_3_1I1R15H_sound : CB4_3_1I1R15H.Encloses (homogeneousEntropy CB4_3_1I1R15Value) := by
  exact contains_sound (homogeneous_enclosed CB4_3_1I1R15Value CB4_3_1I1R15MassTerm_sound CB4_3_1I1R15Entropy_sound) (by decide +kernel)
lemma CB4_3_1I1R16Raw_sound (a : Fin 6) :
    (CB4_3_1I1R16Raw a).Encloses (CB4_3_1I1R16Value a) := by
  exact residualBall_sound_on (below (shape 4 3 1)) B4_3_1Law (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (stageBPriority (shape 4 3 1)) 1 (fun u => B4_3_1Little u ((stageBPriority (shape 4 3 1)) 1)) (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 1) a : ℝ)) (fun u _ => B4_3_1Law_sound u) (fun u _ a => B4_3_1Little_sound u ((stageBPriority (shape 4 3 1)) 1) a) 16 a
lemma CB4_3_1I1R16Certificates_valid :
    CB4_3_1I1R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB4_3_1I1R16P_check : ∀ a : Fin 6, contains (CB4_3_1I1R16Raw a) (CB4_3_1I1R16P a) = true := by
  decide +kernel
lemma CB4_3_1I1R16P_sound (a : Fin 6) :
    (CB4_3_1I1R16P a).Encloses (CB4_3_1I1R16Value a) :=
  contains_sound (CB4_3_1I1R16Raw_sound a) (CB4_3_1I1R16P_check a)
lemma CB4_3_1I1R16Terms_sound (a : Fin 6) :
    (CB4_3_1I1R16Terms a).Encloses (Foundation.entropyTerm (CB4_3_1I1R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_3_1I1R16Certificates_valid
    (CB4_3_1I1R16CertificateIndex a) (CB4_3_1I1R16P_sound a)
lemma CB4_3_1I1R16Entropy_sound : CB4_3_1I1R16Entropy.Encloses (Foundation.finiteEntropy CB4_3_1I1R16Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_3_1I1R16Value CB4_3_1I1R16Terms CB4_3_1I1R16Terms_sound) (by decide +kernel)
lemma CB4_3_1I1R16Mass_sound : CB4_3_1I1R16Mass.Encloses (∑ a, CB4_3_1I1R16Value a) := by
  exact contains_sound (finSumBall_sound 6 CB4_3_1I1R16P CB4_3_1I1R16Value CB4_3_1I1R16P_sound) (by decide +kernel)
lemma CB4_3_1I1R16MassTerm_sound : CB4_3_1I1R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_3_1I1R16Value a))) :=
  entropyTerm_zero_ball (CB4_3_1I1R16Mass_sound)
lemma CB4_3_1I1R16H_sound : CB4_3_1I1R16H.Encloses (homogeneousEntropy CB4_3_1I1R16Value) := by
  exact contains_sound (homogeneous_enclosed CB4_3_1I1R16Value CB4_3_1I1R16MassTerm_sound CB4_3_1I1R16Entropy_sound) (by decide +kernel)
lemma CB4_3_1I1ResidualEntropies_sound (k : Fin 17) :
    (CB4_3_1I1ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 4 3 1)) (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (stageBPriority (shape 4 3 1)) 1 (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 1) a : ℝ)) k)) := by
  fin_cases k
  · exact CB4_3_1I1R0H_sound
  · exact CB4_3_1I1R1H_sound
  · exact CB4_3_1I1R2H_sound
  · exact CB4_3_1I1R3H_sound
  · exact CB4_3_1I1R4H_sound
  · exact CB4_3_1I1R5H_sound
  · exact CB4_3_1I1R6H_sound
  · exact CB4_3_1I1R7H_sound
  · exact CB4_3_1I1R8H_sound
  · exact CB4_3_1I1R9H_sound
  · exact CB4_3_1I1R10H_sound
  · exact CB4_3_1I1R11H_sound
  · exact CB4_3_1I1R12H_sound
  · exact CB4_3_1I1R13H_sound
  · exact CB4_3_1I1R14H_sound
  · exact CB4_3_1I1R15H_sound
  · exact CB4_3_1I1R16H_sound
lemma CB4_3_1I1Group_sound : CB4_3_1I1Group.Encloses
    (groupedEntropy (below (shape 4 3 1)) (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (stageBPriority (shape 4 3 1)) 1 (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 1) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CB4_3_1I1Singleton_sound
    (finSumBall_sound 17 CB4_3_1I1ResidualEntropies _ CB4_3_1I1ResidualEntropies_sound)) (by decide +kernel)

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
lemma CB4_3_1I1_sound_oai : CB4_3_1I1H.Encloses (stageBCapacity (shape 4 3 1) 1) := by
  have hb := contains_sound (Ball.add_sound CB4_3_1I1PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CB4_3_1I1Group_sound)))
    (show contains (.add CB4_3_1I1PairH (.neg (.mul (.exact 2) CB4_3_1I1Group))) CB4_3_1I1H = true by decide +kernel)
  unfold CB4_3_1I1PairValue at hb
  simpa only [stageBCapacity, nativeCapacity,
    show (1 : Fin 3) ≠ 0 by decide, ite_false, if_false, sub_eq_add_neg] using hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_3_1I1_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_3_1I1_sound_oai
