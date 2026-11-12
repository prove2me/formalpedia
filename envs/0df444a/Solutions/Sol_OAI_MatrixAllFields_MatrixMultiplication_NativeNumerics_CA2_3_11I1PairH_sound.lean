-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_3_11I1PairH_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T12:20:19.305823+00:00
-- url     : https://prove2.me/submissions/6defda54-1065-4425-8c58-95f6c718db5e

import Mathlib
import Definitions.Def_OAIQ254M011
import Definitions.Def_OAIQ254M012
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_mul_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkLog_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_CompactCertificate_entropyLookup_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_A2_3_11Law_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_entropyTerm_ball
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_halfTable_sound

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

theorem widen_sound {a b : Ball} {x : ℝ} (hx : a.Encloses x)
    (h : |a.center - b.center| + a.radius ≤ b.radius) : b.Encloses x := by
  have hc : |(a.center : ℝ) - (b.center : ℝ)| + (a.radius : ℝ) ≤ (b.radius : ℝ) := by
    exact_mod_cast h
  unfold Encloses
  calc
    _ = |(x - (a.center : ℝ)) + ((a.center : ℝ) - (b.center : ℝ))| := by congr 1; ring
    _ ≤ |x - (a.center : ℝ)| + |(a.center : ℝ) - (b.center : ℝ)| := abs_add_le _ _
    _ ≤ (a.radius : ℝ) + |(a.center : ℝ) - (b.center : ℝ)| := add_le_add hx (le_refl _)
    _ ≤ _ := by linarith

end Ball

end MatrixMultiplication.AllFieldCertificates

end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.AllFieldCertificates.Replay

open MatrixMultiplication.Foundation.RationalLogCertificate

theorem contains_sound {a b : Ball} {x : ℝ}
    (ha : a.Encloses x) (hab : contains a b = true) : b.Encloses x :=
  Ball.widen_sound ha (of_decide_eq_true hab)

end MatrixMultiplication.AllFieldCertificates.Replay

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

lemma entropyDoublePair_enclosed (p : PairSlot × PairSlot → ℝ)
    (bs : PairSlot × PairSlot → Ball)
    (h : ∀ i, (bs i).Encloses (Foundation.entropyTerm (p i))) :
    (doublePairSumBall bs).Encloses (Foundation.finiteEntropy p) :=
  doublePairSumBall_sound _ _ h

lemma homogeneous_enclosed {A : Type*} [Fintype A] (p : A → ℝ)
    {b e : Ball} (hb : b.Encloses (Foundation.entropyTerm (∑ a, p a)))
    (he : e.Encloses (Foundation.finiteEntropy p)) :
    (Ball.add (Ball.neg b) e).Encloses (homogeneousEntropy p) := by
  convert Ball.add_sound (Ball.neg_sound hb) he using 1
  all_goals try with_reducible_and_instances rfl
  simp only [homogeneousEntropy, Foundation.entropyTerm, neg_mul, neg_neg]

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

lemma halfTable_degree_zero_0 : ∀ t ∈ shapes 8, ∀ ij : PairSlot,
    pairDegree ij ≠ t 0 → halfTable t 0 ij = .exact 0 := by
  decide +kernel
lemma halfTable_degree_zero_1 : ∀ t ∈ shapes 8, ∀ ij : PairSlot,
    pairDegree ij ≠ t 1 → halfTable t 1 ij = .exact 0 := by
  decide +kernel
lemma halfTable_degree_zero_2 : ∀ t ∈ shapes 8, ∀ ij : PairSlot,
    pairDegree ij ≠ t 2 → halfTable t 2 ij = .exact 0 := by
  decide +kernel

lemma halfTable_degree_zero (t : Shape) (ht : t ∈ shapes 8) (w : Fin 3)
    (ij : PairSlot) (h : pairDegree ij ≠ t w) : halfTable t w ij = .exact 0 := by
  fin_cases w
  · exact halfTable_degree_zero_0 t ht ij h
  · exact halfTable_degree_zero_1 t ht ij h
  · exact halfTable_degree_zero_2 t ht ij h

lemma listSumBall_eq_zero {A : Type*} (xs : List A) (b : A → Ball)
    (h : ∀ x ∈ xs, b x = .exact 0) : listSumBall xs b = .exact 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change Ball.add (b x) (listSumBall xs b) = .exact 0
    rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]
    decide +kernel

lemma stageAPairBall_zero (s : Shape) (hs : s ∈ positiveInitial) (bs : Shape → Ball)
    (w : Fin 3) (ij : PairSlot × PairSlot)
    (h : pairDegree ij.1 + pairDegree ij.2 ≠ s w) :
    sparsePairLawBall (below s) s bs (fun u => halfTable u w) ij = .exact 0 := by
  apply listSumBall_eq_zero
  intro u hu
  have hc := stageA_support_complement s hs u hu
  by_cases hl : pairDegree ij.1 = u w
  · have hr : pairDegree ij.2 ≠ (complement s u) w := by
      simp only [complement]
      have hu_le := hc.2 w
      omega
    have hz := halfTable_degree_zero (complement s u)
      (stageA_children_size s hs _ hc.1) w ij.2 hr
    simp only [sparseTripleBall, hz, or_true, ite_true, if_true]
  · have hz := halfTable_degree_zero u (stageA_children_size s hs u hu) w ij.1 hl
    simp only [sparseTripleBall, hz, true_or, ite_true, if_true]

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
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA2_3_11I1
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
lemma CA2_3_11I1PairRaw_sound (a : PairSlot × PairSlot) :
    (CA2_3_11I1PairRaw a).Encloses (CA2_3_11I1PairValue a) := by
  exact stageAPairBall_sound (shape 2 3 11) (by decide +kernel) A2_3_11Law (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (fun u _ => A2_3_11Law_sound u) 1 a
lemma CA2_3_11I1PairCertificates_valid :
    CA2_3_11I1PairCertificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA2_3_11I1PairP_check_0_0 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((0,0),(k,l))) (CA2_3_11I1PairP ((0,0),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_0_1 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((0,1),(k,l))) (CA2_3_11I1PairP ((0,1),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_0_2 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((0,2),(k,l))) (CA2_3_11I1PairP ((0,2),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_0_3 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((0,3),(k,l))) (CA2_3_11I1PairP ((0,3),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_0_4 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((0,4),(k,l))) (CA2_3_11I1PairP ((0,4),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_0_5 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((0,5),(k,l))) (CA2_3_11I1PairP ((0,5),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_1_0 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((1,0),(k,l))) (CA2_3_11I1PairP ((1,0),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_1_1 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((1,1),(k,l))) (CA2_3_11I1PairP ((1,1),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_1_2 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((1,2),(k,l))) (CA2_3_11I1PairP ((1,2),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_1_3 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((1,3),(k,l))) (CA2_3_11I1PairP ((1,3),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_1_4 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((1,4),(k,l))) (CA2_3_11I1PairP ((1,4),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_1_5 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((1,5),(k,l))) (CA2_3_11I1PairP ((1,5),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_2_0 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((2,0),(k,l))) (CA2_3_11I1PairP ((2,0),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_2_1 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((2,1),(k,l))) (CA2_3_11I1PairP ((2,1),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_2_2 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((2,2),(k,l))) (CA2_3_11I1PairP ((2,2),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_2_3 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((2,3),(k,l))) (CA2_3_11I1PairP ((2,3),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_2_4 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((2,4),(k,l))) (CA2_3_11I1PairP ((2,4),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_2_5 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((2,5),(k,l))) (CA2_3_11I1PairP ((2,5),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_3_0 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((3,0),(k,l))) (CA2_3_11I1PairP ((3,0),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_3_1 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((3,1),(k,l))) (CA2_3_11I1PairP ((3,1),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_3_2 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((3,2),(k,l))) (CA2_3_11I1PairP ((3,2),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_3_3 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((3,3),(k,l))) (CA2_3_11I1PairP ((3,3),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_3_4 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((3,4),(k,l))) (CA2_3_11I1PairP ((3,4),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_3_5 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((3,5),(k,l))) (CA2_3_11I1PairP ((3,5),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_4_0 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((4,0),(k,l))) (CA2_3_11I1PairP ((4,0),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_4_1 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((4,1),(k,l))) (CA2_3_11I1PairP ((4,1),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_4_2 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((4,2),(k,l))) (CA2_3_11I1PairP ((4,2),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_4_3 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((4,3),(k,l))) (CA2_3_11I1PairP ((4,3),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_4_4 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((4,4),(k,l))) (CA2_3_11I1PairP ((4,4),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_4_5 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((4,5),(k,l))) (CA2_3_11I1PairP ((4,5),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_5_0 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((5,0),(k,l))) (CA2_3_11I1PairP ((5,0),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_5_1 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((5,1),(k,l))) (CA2_3_11I1PairP ((5,1),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_5_2 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((5,2),(k,l))) (CA2_3_11I1PairP ((5,2),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_5_3 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((5,3),(k,l))) (CA2_3_11I1PairP ((5,3),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_5_4 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((5,4),(k,l))) (CA2_3_11I1PairP ((5,4),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check_5_5 : ∀ k l : Fin 6, contains (CA2_3_11I1PairRaw ((5,5),(k,l))) (CA2_3_11I1PairP ((5,5),(k,l))) = true := by
  decide +kernel
lemma CA2_3_11I1PairP_check (a : PairSlot × PairSlot) : contains (CA2_3_11I1PairRaw a) (CA2_3_11I1PairP a) = true := by
  rcases a with ⟨⟨i,j⟩,⟨k,l⟩⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (CA2_3_11I1PairP_check_0_0 k l) (CA2_3_11I1PairP_check_0_1 k l) (CA2_3_11I1PairP_check_0_2 k l) (CA2_3_11I1PairP_check_0_3 k l) (CA2_3_11I1PairP_check_0_4 k l) (CA2_3_11I1PairP_check_0_5 k l)
  · exact forall_fin6 (CA2_3_11I1PairP_check_1_0 k l) (CA2_3_11I1PairP_check_1_1 k l) (CA2_3_11I1PairP_check_1_2 k l) (CA2_3_11I1PairP_check_1_3 k l) (CA2_3_11I1PairP_check_1_4 k l) (CA2_3_11I1PairP_check_1_5 k l)
  · exact forall_fin6 (CA2_3_11I1PairP_check_2_0 k l) (CA2_3_11I1PairP_check_2_1 k l) (CA2_3_11I1PairP_check_2_2 k l) (CA2_3_11I1PairP_check_2_3 k l) (CA2_3_11I1PairP_check_2_4 k l) (CA2_3_11I1PairP_check_2_5 k l)
  · exact forall_fin6 (CA2_3_11I1PairP_check_3_0 k l) (CA2_3_11I1PairP_check_3_1 k l) (CA2_3_11I1PairP_check_3_2 k l) (CA2_3_11I1PairP_check_3_3 k l) (CA2_3_11I1PairP_check_3_4 k l) (CA2_3_11I1PairP_check_3_5 k l)
  · exact forall_fin6 (CA2_3_11I1PairP_check_4_0 k l) (CA2_3_11I1PairP_check_4_1 k l) (CA2_3_11I1PairP_check_4_2 k l) (CA2_3_11I1PairP_check_4_3 k l) (CA2_3_11I1PairP_check_4_4 k l) (CA2_3_11I1PairP_check_4_5 k l)
  · exact forall_fin6 (CA2_3_11I1PairP_check_5_0 k l) (CA2_3_11I1PairP_check_5_1 k l) (CA2_3_11I1PairP_check_5_2 k l) (CA2_3_11I1PairP_check_5_3 k l) (CA2_3_11I1PairP_check_5_4 k l) (CA2_3_11I1PairP_check_5_5 k l)
lemma CA2_3_11I1PairP_sound (a : PairSlot × PairSlot) :
    (CA2_3_11I1PairP a).Encloses (CA2_3_11I1PairValue a) :=
  contains_sound (CA2_3_11I1PairRaw_sound a) (CA2_3_11I1PairP_check a)
lemma CA2_3_11I1PairTerms_sound (a : PairSlot × PairSlot) :
    (CA2_3_11I1PairTerms a).Encloses (Foundation.entropyTerm (CA2_3_11I1PairValue a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_3_11I1PairCertificates_valid
    (CA2_3_11I1PairCertificateIndex a) (CA2_3_11I1PairP_sound a)
lemma CA2_3_11I1PairEntropy_sound : CA2_3_11I1PairEntropy.Encloses (Foundation.finiteEntropy CA2_3_11I1PairValue) := by
  exact contains_sound (entropyDoublePair_enclosed CA2_3_11I1PairValue CA2_3_11I1PairTerms CA2_3_11I1PairTerms_sound) (by decide +kernel)
lemma CA2_3_11I1PairMass_sound : CA2_3_11I1PairMass.Encloses (∑ a, CA2_3_11I1PairValue a) := by
  exact contains_sound (doublePairSumBall_sound CA2_3_11I1PairP CA2_3_11I1PairValue CA2_3_11I1PairP_sound) (by decide +kernel)
lemma CA2_3_11I1PairMassTermLog_sound : CA2_3_11I1PairMassTermLog.Encloses (Real.log ((∑ a, CA2_3_11I1PairValue a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_3_11I1PairMass_sound) (w := CA2_3_11I1PairMassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CA2_3_11I1PairMassTerm_sound : CA2_3_11I1PairMassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_3_11I1PairValue a))) := by
  exact contains_sound (entropyTerm_ball (CA2_3_11I1PairMass_sound) CA2_3_11I1PairMassTermLog_sound) (by decide +kernel)
lemma CA2_3_11I1PairH_sound_oai : CA2_3_11I1PairH.Encloses (homogeneousEntropy CA2_3_11I1PairValue) := by
  exact contains_sound (homogeneous_enclosed CA2_3_11I1PairValue CA2_3_11I1PairMassTerm_sound CA2_3_11I1PairEntropy_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_3_11I1PairH_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_3_11I1PairH_sound_oai
