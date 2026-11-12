-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_4_9I2PairP_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:32:53.746197+00:00
-- url     : https://prove2.me/submissions/497d4f2c-9d22-4974-a746-fb76c5427d02

import Mathlib
import Definitions.Def_OAIQ254M012
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_inv_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_mul_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_A3_4_9Den_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_A3_4_9Raw_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA3_4_9I2PairP_check
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_halfTable_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_stageAPairBall_zero

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
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators

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

lemma sparseTripleBall_eq (a b c : Ball) :
    sparseTripleBall a b c = .mul (.mul a b) c := by
  unfold sparseTripleBall
  split_ifs with h
  · rcases h with h | h
    · subst b
      cases a
      cases c
      simp [Ball.mul, Ball.exact]
    · subst c
      cases a
      cases b
      simp [Ball.mul, Ball.exact]
  · rfl

lemma sparsePairLawBall_eq {A : Type*} (support : List Shape) (s : Shape)
    (p : Shape → Ball) (q : Shape → A → Ball) (ij : A × A) :
    sparsePairLawBall support s p q ij = pairLawBall support s p q ij := by
  simp only [sparsePairLawBall, sparseTripleBall_eq, pairLawBall]

lemma sparsePairLawBall_sound_on {A : Type*} [Fintype A] (support : List Shape) (s : Shape)
    (bs : Shape → Ball) (p : Shape → ℝ) (bq : Shape → A → Ball) (q : Shape → A → ℝ)
    (hp : ∀ u ∈ support, (bs u).Encloses (p u))
    (hq : ∀ u ∈ support, ∀ a, (bq u a).Encloses (q u a))
    (hcq : ∀ u ∈ support, ∀ a, (bq (complement s u) a).Encloses (q (complement s u) a))
    (ij : A × A) :
    (sparsePairLawBall support s bs bq ij).Encloses (pairLaw support s p q ij) := by
  rw [sparsePairLawBall_eq]
  exact pairLawBall_sound_on support s bs p bq q hp hq hcq ij

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
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SupportedContraction
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

lemma stageAPairBall_eq (s : Shape) (hs : s ∈ positiveInitial) (bs : Shape → Ball)
    (w : Fin 3) (ij : PairSlot × PairSlot) :
    stageAPairBall s bs w ij =
      sparsePairLawBall (below s) s bs (fun u => halfTable u w) ij := by
  unfold stageAPairBall
  split_ifs with h
  · rfl
  · exact (stageAPairBall_zero s hs bs w ij h).symm

lemma stageAPairBall_sound (s : Shape) (hs : s ∈ positiveInitial)
    (bs : Shape → Ball) (p : Shape → ℝ)
    (hp : ∀ u ∈ below s, (bs u).Encloses (p u)) (w : Fin 3) (ij : PairSlot × PairSlot) :
    (stageAPairBall s bs w ij).Encloses
      (pairLaw (below s) s p (fun u a => (halfLaw u w a : ℝ)) ij) := by
  rw [stageAPairBall_eq s hs]
  exact sparsePairLawBall_sound_on (below s) s bs p (fun u => halfTable u w)
    (fun u a => (halfLaw u w a : ℝ)) hp
    (fun u hu a => halfTable_sound u (stageA_children_size s hs u hu) w a)
    (fun u hu a => halfTable_sound (complement s u)
      (stageA_children_size s hs _ (stageA_support_complement s hs u hu).1) w a) ij

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA3_4_9I2Pair
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
lemma CA3_4_9I2PairRaw_sound (a : PairSlot × PairSlot) :
    (CA3_4_9I2PairRaw a).Encloses (CA3_4_9I2PairValue a) := by
  exact stageAPairBall_sound (shape 3 4 9) (by decide +kernel) A3_4_9Law (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (fun u _ => A3_4_9Law_sound u) 2 a
lemma CA3_4_9I2PairP_sound_oai (a : PairSlot × PairSlot) :
    (CA3_4_9I2PairP a).Encloses (CA3_4_9I2PairValue a) :=
  contains_sound (CA3_4_9I2PairRaw_sound a) (CA3_4_9I2PairP_check a)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_4_9I2PairP_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_4_9I2PairP_sound_oai
