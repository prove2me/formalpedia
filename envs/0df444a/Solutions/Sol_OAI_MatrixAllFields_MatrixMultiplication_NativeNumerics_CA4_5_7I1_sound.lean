-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_5_7I1_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:26:02.626208+00:00
-- url     : https://prove2.me/submissions/9ff09c70-4d11-46f7-be59-144814f3fa6c

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
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_A4_5_7Law_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA4_5_7I1ResidualEntropies_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA4_5_7I1Singles_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_entropyDoublePair_enclosed
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_entropyTerm_ball
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_halfTable_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_homogeneous_enclosed
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

lemma forall_fin6 {P : Fin 6 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2)
    (h3 : P 3) (h4 : P 4) (h5 : P 5) : ∀ i, P i := by
  intro i
  fin_cases i <;> assumption

lemma pairSumBall_sound (bs : PairSlot → Ball) (v : PairSlot → ℝ)
    (h : ∀ a, (bs a).Encloses (v a)) :
    (pairSumBall bs).Encloses (∑ a, v a) := by
  exact product_fin6_enclosed _ _ (fun i j => h (i,j))

lemma doublePairSumBall_sound (bs : PairSlot × PairSlot → Ball)
    (v : PairSlot × PairSlot → ℝ) (h : ∀ a, (bs a).Encloses (v a)) :
    (doublePairSumBall bs).Encloses (∑ a, v a) := by
  rw [Fintype.sum_prod_type]
  exact pairSumBall_sound _ _ (fun i => pairSumBall_sound _ _ (fun j => h (i,j)))

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
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA4_5_7I1
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
lemma CA4_5_7I1PairRaw_sound (a : PairSlot × PairSlot) :
    (CA4_5_7I1PairRaw a).Encloses (CA4_5_7I1PairValue a) := by
  exact stageAPairBall_sound (shape 4 5 7) (by decide +kernel) A4_5_7Law (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (fun u _ => A4_5_7Law_sound u) 1 a
lemma CA4_5_7I1PairCertificates_valid :
    CA4_5_7I1PairCertificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA4_5_7I1PairP_check_0_0 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((0,0),(k,l))) (CA4_5_7I1PairP ((0,0),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_0_1 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((0,1),(k,l))) (CA4_5_7I1PairP ((0,1),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_0_2 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((0,2),(k,l))) (CA4_5_7I1PairP ((0,2),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_0_3 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((0,3),(k,l))) (CA4_5_7I1PairP ((0,3),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_0_4 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((0,4),(k,l))) (CA4_5_7I1PairP ((0,4),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_0_5 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((0,5),(k,l))) (CA4_5_7I1PairP ((0,5),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_1_0 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((1,0),(k,l))) (CA4_5_7I1PairP ((1,0),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_1_1 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((1,1),(k,l))) (CA4_5_7I1PairP ((1,1),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_1_2 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((1,2),(k,l))) (CA4_5_7I1PairP ((1,2),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_1_3 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((1,3),(k,l))) (CA4_5_7I1PairP ((1,3),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_1_4 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((1,4),(k,l))) (CA4_5_7I1PairP ((1,4),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_1_5 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((1,5),(k,l))) (CA4_5_7I1PairP ((1,5),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_2_0 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((2,0),(k,l))) (CA4_5_7I1PairP ((2,0),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_2_1 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((2,1),(k,l))) (CA4_5_7I1PairP ((2,1),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_2_2 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((2,2),(k,l))) (CA4_5_7I1PairP ((2,2),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_2_3 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((2,3),(k,l))) (CA4_5_7I1PairP ((2,3),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_2_4 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((2,4),(k,l))) (CA4_5_7I1PairP ((2,4),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_2_5 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((2,5),(k,l))) (CA4_5_7I1PairP ((2,5),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_3_0 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((3,0),(k,l))) (CA4_5_7I1PairP ((3,0),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_3_1 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((3,1),(k,l))) (CA4_5_7I1PairP ((3,1),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_3_2 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((3,2),(k,l))) (CA4_5_7I1PairP ((3,2),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_3_3 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((3,3),(k,l))) (CA4_5_7I1PairP ((3,3),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_3_4 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((3,4),(k,l))) (CA4_5_7I1PairP ((3,4),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_3_5 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((3,5),(k,l))) (CA4_5_7I1PairP ((3,5),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_4_0 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((4,0),(k,l))) (CA4_5_7I1PairP ((4,0),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_4_1 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((4,1),(k,l))) (CA4_5_7I1PairP ((4,1),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_4_2 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((4,2),(k,l))) (CA4_5_7I1PairP ((4,2),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_4_3 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((4,3),(k,l))) (CA4_5_7I1PairP ((4,3),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_4_4 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((4,4),(k,l))) (CA4_5_7I1PairP ((4,4),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_4_5 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((4,5),(k,l))) (CA4_5_7I1PairP ((4,5),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_5_0 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((5,0),(k,l))) (CA4_5_7I1PairP ((5,0),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_5_1 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((5,1),(k,l))) (CA4_5_7I1PairP ((5,1),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_5_2 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((5,2),(k,l))) (CA4_5_7I1PairP ((5,2),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_5_3 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((5,3),(k,l))) (CA4_5_7I1PairP ((5,3),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_5_4 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((5,4),(k,l))) (CA4_5_7I1PairP ((5,4),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check_5_5 : ∀ k l : Fin 6, contains (CA4_5_7I1PairRaw ((5,5),(k,l))) (CA4_5_7I1PairP ((5,5),(k,l))) = true := by
  decide +kernel
lemma CA4_5_7I1PairP_check (a : PairSlot × PairSlot) : contains (CA4_5_7I1PairRaw a) (CA4_5_7I1PairP a) = true := by
  rcases a with ⟨⟨i,j⟩,⟨k,l⟩⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (CA4_5_7I1PairP_check_0_0 k l) (CA4_5_7I1PairP_check_0_1 k l) (CA4_5_7I1PairP_check_0_2 k l) (CA4_5_7I1PairP_check_0_3 k l) (CA4_5_7I1PairP_check_0_4 k l) (CA4_5_7I1PairP_check_0_5 k l)
  · exact forall_fin6 (CA4_5_7I1PairP_check_1_0 k l) (CA4_5_7I1PairP_check_1_1 k l) (CA4_5_7I1PairP_check_1_2 k l) (CA4_5_7I1PairP_check_1_3 k l) (CA4_5_7I1PairP_check_1_4 k l) (CA4_5_7I1PairP_check_1_5 k l)
  · exact forall_fin6 (CA4_5_7I1PairP_check_2_0 k l) (CA4_5_7I1PairP_check_2_1 k l) (CA4_5_7I1PairP_check_2_2 k l) (CA4_5_7I1PairP_check_2_3 k l) (CA4_5_7I1PairP_check_2_4 k l) (CA4_5_7I1PairP_check_2_5 k l)
  · exact forall_fin6 (CA4_5_7I1PairP_check_3_0 k l) (CA4_5_7I1PairP_check_3_1 k l) (CA4_5_7I1PairP_check_3_2 k l) (CA4_5_7I1PairP_check_3_3 k l) (CA4_5_7I1PairP_check_3_4 k l) (CA4_5_7I1PairP_check_3_5 k l)
  · exact forall_fin6 (CA4_5_7I1PairP_check_4_0 k l) (CA4_5_7I1PairP_check_4_1 k l) (CA4_5_7I1PairP_check_4_2 k l) (CA4_5_7I1PairP_check_4_3 k l) (CA4_5_7I1PairP_check_4_4 k l) (CA4_5_7I1PairP_check_4_5 k l)
  · exact forall_fin6 (CA4_5_7I1PairP_check_5_0 k l) (CA4_5_7I1PairP_check_5_1 k l) (CA4_5_7I1PairP_check_5_2 k l) (CA4_5_7I1PairP_check_5_3 k l) (CA4_5_7I1PairP_check_5_4 k l) (CA4_5_7I1PairP_check_5_5 k l)
lemma CA4_5_7I1PairP_sound (a : PairSlot × PairSlot) :
    (CA4_5_7I1PairP a).Encloses (CA4_5_7I1PairValue a) :=
  contains_sound (CA4_5_7I1PairRaw_sound a) (CA4_5_7I1PairP_check a)
lemma CA4_5_7I1PairTerms_sound (a : PairSlot × PairSlot) :
    (CA4_5_7I1PairTerms a).Encloses (Foundation.entropyTerm (CA4_5_7I1PairValue a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_5_7I1PairCertificates_valid
    (CA4_5_7I1PairCertificateIndex a) (CA4_5_7I1PairP_sound a)
lemma CA4_5_7I1PairEntropy_sound : CA4_5_7I1PairEntropy.Encloses (Foundation.finiteEntropy CA4_5_7I1PairValue) := by
  exact contains_sound (entropyDoublePair_enclosed CA4_5_7I1PairValue CA4_5_7I1PairTerms CA4_5_7I1PairTerms_sound) (by decide +kernel)
lemma CA4_5_7I1PairMass_sound : CA4_5_7I1PairMass.Encloses (∑ a, CA4_5_7I1PairValue a) := by
  exact contains_sound (doublePairSumBall_sound CA4_5_7I1PairP CA4_5_7I1PairValue CA4_5_7I1PairP_sound) (by decide +kernel)
lemma CA4_5_7I1PairMassTermLog_sound : CA4_5_7I1PairMassTermLog.Encloses (Real.log ((∑ a, CA4_5_7I1PairValue a))) := by
  exact checkLog_sound logTwoBall_sound (CA4_5_7I1PairMass_sound) (w := CA4_5_7I1PairMassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CA4_5_7I1PairMassTerm_sound : CA4_5_7I1PairMassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_5_7I1PairValue a))) := by
  exact contains_sound (entropyTerm_ball (CA4_5_7I1PairMass_sound) CA4_5_7I1PairMassTermLog_sound) (by decide +kernel)
lemma CA4_5_7I1PairH_sound : CA4_5_7I1PairH.Encloses (homogeneousEntropy CA4_5_7I1PairValue) := by
  exact contains_sound (homogeneous_enclosed CA4_5_7I1PairValue CA4_5_7I1PairMassTerm_sound CA4_5_7I1PairEntropy_sound) (by decide +kernel)

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
lemma CA4_5_7I1Singleton_sound : CA4_5_7I1Singleton.Encloses
    (singletonEntropy (below (shape 4 5 7)) (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 4 5 7)) A4_5_7Law (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 1
    CA4_5_7I1Singles (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A4_5_7Law_sound u) CA4_5_7I1Singles_sound) (by decide +kernel)
lemma CA4_5_7I1Group_sound : CA4_5_7I1Group.Encloses
    (groupedEntropy (below (shape 4 5 7)) (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CA4_5_7I1Singleton_sound
    (finSumBall_sound 17 CA4_5_7I1ResidualEntropies _ CA4_5_7I1ResidualEntropies_sound)) (by decide +kernel)

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
lemma CA4_5_7I1_sound_oai : CA4_5_7I1H.Encloses (stageACapacity (shape 4 5 7) 1) := by
  have hb := contains_sound (Ball.add_sound CA4_5_7I1PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CA4_5_7I1Group_sound)))
    (show contains (.add CA4_5_7I1PairH (.neg (.mul (.exact 2) CA4_5_7I1Group))) CA4_5_7I1H = true by decide +kernel)
  unfold CA4_5_7I1PairValue at hb
  simpa only [stageACapacity, nativeCapacity,
    show (1 : Fin 3) ≠ 0 by decide, ite_false, if_false, sub_eq_add_neg] using hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_5_7I1_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_5_7I1_sound_oai
