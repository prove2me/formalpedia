-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_3_1I1R10H_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:17:36.859114+00:00
-- url     : https://prove2.me/submissions/847594a5-04a5-4ea7-bae5-fa88da87e678

import Mathlib
import Definitions.Def_OAIQ254M011
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_inv_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_mul_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_finSumBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_CompactCertificate_entropyLookup_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B4_3_1Den_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B4_3_1Raw_sound
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
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
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

lemma entropyFin_enclosed (n : ℕ) (p : Fin n → ℝ) (bs : Fin n → Ball)
    (h : ∀ i, (bs i).Encloses (Foundation.entropyTerm (p i))) :
    (finSumBall n bs).Encloses (Foundation.finiteEntropy p) :=
  finSumBall_sound n _ _ h

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
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
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
lemma CB4_3_1I1R10Raw_sound (a : Fin 6) :
    (CB4_3_1I1R10Raw a).Encloses (CB4_3_1I1R10Value a) := by
  exact residualBall_sound_on (below (shape 4 3 1)) B4_3_1Law (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (stageBPriority (shape 4 3 1)) 1 (fun u => B4_3_1Little u ((stageBPriority (shape 4 3 1)) 1)) (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 1) a : ℝ)) (fun u _ => B4_3_1Law_sound u) (fun u _ a => B4_3_1Little_sound u ((stageBPriority (shape 4 3 1)) 1) a) 10 a
lemma CB4_3_1I1R10Certificates_valid :
    CB4_3_1I1R10Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB4_3_1I1R10P_check : ∀ a : Fin 6, contains (CB4_3_1I1R10Raw a) (CB4_3_1I1R10P a) = true := by
  decide +kernel
lemma CB4_3_1I1R10P_sound (a : Fin 6) :
    (CB4_3_1I1R10P a).Encloses (CB4_3_1I1R10Value a) :=
  contains_sound (CB4_3_1I1R10Raw_sound a) (CB4_3_1I1R10P_check a)
lemma CB4_3_1I1R10Terms_sound (a : Fin 6) :
    (CB4_3_1I1R10Terms a).Encloses (Foundation.entropyTerm (CB4_3_1I1R10Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_3_1I1R10Certificates_valid
    (CB4_3_1I1R10CertificateIndex a) (CB4_3_1I1R10P_sound a)
lemma CB4_3_1I1R10Entropy_sound : CB4_3_1I1R10Entropy.Encloses (Foundation.finiteEntropy CB4_3_1I1R10Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB4_3_1I1R10Value CB4_3_1I1R10Terms CB4_3_1I1R10Terms_sound) (by decide +kernel)
lemma CB4_3_1I1R10Mass_sound : CB4_3_1I1R10Mass.Encloses (∑ a, CB4_3_1I1R10Value a) := by
  exact contains_sound (finSumBall_sound 6 CB4_3_1I1R10P CB4_3_1I1R10Value CB4_3_1I1R10P_sound) (by decide +kernel)
lemma CB4_3_1I1R10MassTerm_sound : CB4_3_1I1R10MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_3_1I1R10Value a))) :=
  entropyTerm_zero_ball (CB4_3_1I1R10Mass_sound)
lemma CB4_3_1I1R10H_sound_oai : CB4_3_1I1R10H.Encloses (homogeneousEntropy CB4_3_1I1R10Value) := by
  exact contains_sound (homogeneous_enclosed CB4_3_1I1R10Value CB4_3_1I1R10MassTerm_sound CB4_3_1I1R10Entropy_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_3_1I1R10H_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_3_1I1R10H_sound_oai
