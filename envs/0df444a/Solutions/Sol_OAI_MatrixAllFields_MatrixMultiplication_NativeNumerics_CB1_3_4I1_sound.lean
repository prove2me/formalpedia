-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB1_3_4I1_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T07:19:37.199046+00:00
-- url     : https://prove2.me/submissions/cd9eb4a1-ea01-4653-9240-a1bc8fedb746

import Mathlib
import Definitions.Def_OAIQ254M010
import Definitions.Def_OAIQ254M011
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_mul_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkLog_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_CompactCertificate_entropyLookup_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B1_3_4Law_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_entropyTerm_ball

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

lemma log_exact_one_ball {p : ℝ} (hp : (Ball.exact 1).Encloses p) :
    (Ball.exact 0).Encloses (Real.log p) := by
  have hb := Ball.bounds hp
  have h : p = 1 := by norm_num [Ball.lower, Ball.upper, Ball.exact] at hb <;> linarith
  rw [h, Real.log_one]
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
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitB1_3_4
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

lemma B1_3_4_below : below (shape 1 3 4) = [
  (shape 0 0 4),
  (shape 0 1 3),
  (shape 0 2 2),
  (shape 0 3 1),
  (shape 1 0 3),
  (shape 1 1 2),
  (shape 1 2 1),
  (shape 1 3 0)] := by decide +kernel

end MatrixMultiplication.NativeNumerics

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

namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
lemma B1_3_4Binary_eq (u : Shape) (hu : u ∈ shapes 4) :
    binaryParameter (shape 1 3 4) u = B1_3_4Binary u := by
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

lemma B1_3_4Little_sound (u : Shape) (w : Fin 3) (i : Fin 6) :
    (B1_3_4Little u w i).Encloses (littleLaw (shape 1 3 4) u w i : ℝ) := by
  by_cases hu : u ∈ shapes 4
  · simp only [B1_3_4Little, hu, ite_true, if_true]
    apply exact_rat_enclosed
    simp only [B1_3_4LittleRat, littleLaw, B1_3_4Binary_eq u hu]
  · simp only [B1_3_4Little, hu, ite_false, if_false]
    exact Ball.exact_sound _

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB1_3_4I1
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
lemma CB1_3_4I1PairRaw_sound (a : PairSlot) :
    (CB1_3_4I1PairRaw a).Encloses (CB1_3_4I1PairValue a) := by
  exact pairLawBall_sound_on (below (shape 1 3 4)) (shape 1 3 4) B1_3_4Law (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (fun u => B1_3_4Little u ((stageBPriority (shape 1 3 4)) 1)) (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 1) a : ℝ)) (fun u _ => B1_3_4Law_sound u) (fun u _ a => B1_3_4Little_sound u ((stageBPriority (shape 1 3 4)) 1) a) (fun u _ a => B1_3_4Little_sound (complement (shape 1 3 4) u) ((stageBPriority (shape 1 3 4)) 1) a) a
lemma CB1_3_4I1PairCertificates_valid :
    CB1_3_4I1PairCertificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB1_3_4I1PairP_check : ∀ a : PairSlot, contains (CB1_3_4I1PairRaw a) (CB1_3_4I1PairP a) = true := by
  decide +kernel
lemma CB1_3_4I1PairP_sound (a : PairSlot) :
    (CB1_3_4I1PairP a).Encloses (CB1_3_4I1PairValue a) :=
  contains_sound (CB1_3_4I1PairRaw_sound a) (CB1_3_4I1PairP_check a)
lemma CB1_3_4I1PairTerms_sound (a : PairSlot) :
    (CB1_3_4I1PairTerms a).Encloses (Foundation.entropyTerm (CB1_3_4I1PairValue a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_3_4I1PairCertificates_valid
    (CB1_3_4I1PairCertificateIndex a) (CB1_3_4I1PairP_sound a)
lemma CB1_3_4I1PairEntropy_sound : CB1_3_4I1PairEntropy.Encloses (Foundation.finiteEntropy CB1_3_4I1PairValue) := by
  exact contains_sound (entropyPair_enclosed CB1_3_4I1PairValue CB1_3_4I1PairTerms CB1_3_4I1PairTerms_sound) (by decide +kernel)
lemma CB1_3_4I1PairMass_sound : CB1_3_4I1PairMass.Encloses (∑ a, CB1_3_4I1PairValue a) := by
  exact contains_sound (pairSumBall_sound CB1_3_4I1PairP CB1_3_4I1PairValue CB1_3_4I1PairP_sound) (by decide +kernel)
lemma CB1_3_4I1PairMassTermLog_sound : CB1_3_4I1PairMassTermLog.Encloses (Real.log ((∑ a, CB1_3_4I1PairValue a))) := by
  exact checkLog_sound logTwoBall_sound (CB1_3_4I1PairMass_sound) (w := CB1_3_4I1PairMassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CB1_3_4I1PairMassTerm_sound : CB1_3_4I1PairMassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_3_4I1PairValue a))) := by
  exact contains_sound (entropyTerm_ball (CB1_3_4I1PairMass_sound) CB1_3_4I1PairMassTermLog_sound) (by decide +kernel)
lemma CB1_3_4I1PairH_sound : CB1_3_4I1PairH.Encloses (homogeneousEntropy CB1_3_4I1PairValue) := by
  exact contains_sound (homogeneous_enclosed CB1_3_4I1PairValue CB1_3_4I1PairMassTerm_sound CB1_3_4I1PairEntropy_sound) (by decide +kernel)

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
lemma CB1_3_4I1R0Raw_sound (a : Fin 6) :
    (CB1_3_4I1R0Raw a).Encloses (CB1_3_4I1R0Value a) := by
  exact residualBall_sound_on (below (shape 1 3 4)) B1_3_4Law (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 1 (fun u => B1_3_4Little u ((stageBPriority (shape 1 3 4)) 1)) (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 1) a : ℝ)) (fun u _ => B1_3_4Law_sound u) (fun u _ a => B1_3_4Little_sound u ((stageBPriority (shape 1 3 4)) 1) a) 0 a
lemma CB1_3_4I1R0Certificates_valid :
    CB1_3_4I1R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB1_3_4I1R0P_check : ∀ a : Fin 6, contains (CB1_3_4I1R0Raw a) (CB1_3_4I1R0P a) = true := by
  decide +kernel
lemma CB1_3_4I1R0P_sound (a : Fin 6) :
    (CB1_3_4I1R0P a).Encloses (CB1_3_4I1R0Value a) :=
  contains_sound (CB1_3_4I1R0Raw_sound a) (CB1_3_4I1R0P_check a)
lemma CB1_3_4I1R0Terms_sound (a : Fin 6) :
    (CB1_3_4I1R0Terms a).Encloses (Foundation.entropyTerm (CB1_3_4I1R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_3_4I1R0Certificates_valid
    (CB1_3_4I1R0CertificateIndex a) (CB1_3_4I1R0P_sound a)
lemma CB1_3_4I1R0Entropy_sound : CB1_3_4I1R0Entropy.Encloses (Foundation.finiteEntropy CB1_3_4I1R0Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_3_4I1R0Value CB1_3_4I1R0Terms CB1_3_4I1R0Terms_sound) (by decide +kernel)
lemma CB1_3_4I1R0Mass_sound : CB1_3_4I1R0Mass.Encloses (∑ a, CB1_3_4I1R0Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_3_4I1R0P CB1_3_4I1R0Value CB1_3_4I1R0P_sound) (by decide +kernel)
lemma CB1_3_4I1R0MassTermLog_sound : CB1_3_4I1R0MassTermLog.Encloses (Real.log ((∑ a, CB1_3_4I1R0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB1_3_4I1R0Mass_sound) (w := CB1_3_4I1R0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CB1_3_4I1R0MassTerm_sound : CB1_3_4I1R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_3_4I1R0Value a))) := by
  exact contains_sound (entropyTerm_ball (CB1_3_4I1R0Mass_sound) CB1_3_4I1R0MassTermLog_sound) (by decide +kernel)
lemma CB1_3_4I1R0H_sound : CB1_3_4I1R0H.Encloses (homogeneousEntropy CB1_3_4I1R0Value) := by
  exact contains_sound (homogeneous_enclosed CB1_3_4I1R0Value CB1_3_4I1R0MassTerm_sound CB1_3_4I1R0Entropy_sound) (by decide +kernel)
lemma CB1_3_4I1R1Raw_sound (a : Fin 6) :
    (CB1_3_4I1R1Raw a).Encloses (CB1_3_4I1R1Value a) := by
  exact residualBall_sound_on (below (shape 1 3 4)) B1_3_4Law (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 1 (fun u => B1_3_4Little u ((stageBPriority (shape 1 3 4)) 1)) (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 1) a : ℝ)) (fun u _ => B1_3_4Law_sound u) (fun u _ a => B1_3_4Little_sound u ((stageBPriority (shape 1 3 4)) 1) a) 1 a
lemma CB1_3_4I1R1Certificates_valid :
    CB1_3_4I1R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB1_3_4I1R1P_check : ∀ a : Fin 6, contains (CB1_3_4I1R1Raw a) (CB1_3_4I1R1P a) = true := by
  decide +kernel
lemma CB1_3_4I1R1P_sound (a : Fin 6) :
    (CB1_3_4I1R1P a).Encloses (CB1_3_4I1R1Value a) :=
  contains_sound (CB1_3_4I1R1Raw_sound a) (CB1_3_4I1R1P_check a)
lemma CB1_3_4I1R1Terms_sound (a : Fin 6) :
    (CB1_3_4I1R1Terms a).Encloses (Foundation.entropyTerm (CB1_3_4I1R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_3_4I1R1Certificates_valid
    (CB1_3_4I1R1CertificateIndex a) (CB1_3_4I1R1P_sound a)
lemma CB1_3_4I1R1Entropy_sound : CB1_3_4I1R1Entropy.Encloses (Foundation.finiteEntropy CB1_3_4I1R1Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_3_4I1R1Value CB1_3_4I1R1Terms CB1_3_4I1R1Terms_sound) (by decide +kernel)
lemma CB1_3_4I1R1Mass_sound : CB1_3_4I1R1Mass.Encloses (∑ a, CB1_3_4I1R1Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_3_4I1R1P CB1_3_4I1R1Value CB1_3_4I1R1P_sound) (by decide +kernel)
lemma CB1_3_4I1R1MassTermLog_sound : CB1_3_4I1R1MassTermLog.Encloses (Real.log ((∑ a, CB1_3_4I1R1Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB1_3_4I1R1Mass_sound) (w := CB1_3_4I1R1MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CB1_3_4I1R1MassTerm_sound : CB1_3_4I1R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_3_4I1R1Value a))) := by
  exact contains_sound (entropyTerm_ball (CB1_3_4I1R1Mass_sound) CB1_3_4I1R1MassTermLog_sound) (by decide +kernel)
lemma CB1_3_4I1R1H_sound : CB1_3_4I1R1H.Encloses (homogeneousEntropy CB1_3_4I1R1Value) := by
  exact contains_sound (homogeneous_enclosed CB1_3_4I1R1Value CB1_3_4I1R1MassTerm_sound CB1_3_4I1R1Entropy_sound) (by decide +kernel)
lemma CB1_3_4I1R2Raw_sound (a : Fin 6) :
    (CB1_3_4I1R2Raw a).Encloses (CB1_3_4I1R2Value a) := by
  exact residualBall_sound_on (below (shape 1 3 4)) B1_3_4Law (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 1 (fun u => B1_3_4Little u ((stageBPriority (shape 1 3 4)) 1)) (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 1) a : ℝ)) (fun u _ => B1_3_4Law_sound u) (fun u _ a => B1_3_4Little_sound u ((stageBPriority (shape 1 3 4)) 1) a) 2 a
lemma CB1_3_4I1R2Certificates_valid :
    CB1_3_4I1R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB1_3_4I1R2P_check : ∀ a : Fin 6, contains (CB1_3_4I1R2Raw a) (CB1_3_4I1R2P a) = true := by
  decide +kernel
lemma CB1_3_4I1R2P_sound (a : Fin 6) :
    (CB1_3_4I1R2P a).Encloses (CB1_3_4I1R2Value a) :=
  contains_sound (CB1_3_4I1R2Raw_sound a) (CB1_3_4I1R2P_check a)
lemma CB1_3_4I1R2Terms_sound (a : Fin 6) :
    (CB1_3_4I1R2Terms a).Encloses (Foundation.entropyTerm (CB1_3_4I1R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_3_4I1R2Certificates_valid
    (CB1_3_4I1R2CertificateIndex a) (CB1_3_4I1R2P_sound a)
lemma CB1_3_4I1R2Entropy_sound : CB1_3_4I1R2Entropy.Encloses (Foundation.finiteEntropy CB1_3_4I1R2Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_3_4I1R2Value CB1_3_4I1R2Terms CB1_3_4I1R2Terms_sound) (by decide +kernel)
lemma CB1_3_4I1R2Mass_sound : CB1_3_4I1R2Mass.Encloses (∑ a, CB1_3_4I1R2Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_3_4I1R2P CB1_3_4I1R2Value CB1_3_4I1R2P_sound) (by decide +kernel)
lemma CB1_3_4I1R2MassTermLog_sound : CB1_3_4I1R2MassTermLog.Encloses (Real.log ((∑ a, CB1_3_4I1R2Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB1_3_4I1R2Mass_sound) (w := CB1_3_4I1R2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CB1_3_4I1R2MassTerm_sound : CB1_3_4I1R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_3_4I1R2Value a))) := by
  exact contains_sound (entropyTerm_ball (CB1_3_4I1R2Mass_sound) CB1_3_4I1R2MassTermLog_sound) (by decide +kernel)
lemma CB1_3_4I1R2H_sound : CB1_3_4I1R2H.Encloses (homogeneousEntropy CB1_3_4I1R2Value) := by
  exact contains_sound (homogeneous_enclosed CB1_3_4I1R2Value CB1_3_4I1R2MassTerm_sound CB1_3_4I1R2Entropy_sound) (by decide +kernel)
lemma CB1_3_4I1R3Raw_sound (a : Fin 6) :
    (CB1_3_4I1R3Raw a).Encloses (CB1_3_4I1R3Value a) := by
  exact residualBall_sound_on (below (shape 1 3 4)) B1_3_4Law (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 1 (fun u => B1_3_4Little u ((stageBPriority (shape 1 3 4)) 1)) (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 1) a : ℝ)) (fun u _ => B1_3_4Law_sound u) (fun u _ a => B1_3_4Little_sound u ((stageBPriority (shape 1 3 4)) 1) a) 3 a
lemma CB1_3_4I1R3Certificates_valid :
    CB1_3_4I1R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB1_3_4I1R3P_check : ∀ a : Fin 6, contains (CB1_3_4I1R3Raw a) (CB1_3_4I1R3P a) = true := by
  decide +kernel
lemma CB1_3_4I1R3P_sound (a : Fin 6) :
    (CB1_3_4I1R3P a).Encloses (CB1_3_4I1R3Value a) :=
  contains_sound (CB1_3_4I1R3Raw_sound a) (CB1_3_4I1R3P_check a)
lemma CB1_3_4I1R3Terms_sound (a : Fin 6) :
    (CB1_3_4I1R3Terms a).Encloses (Foundation.entropyTerm (CB1_3_4I1R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_3_4I1R3Certificates_valid
    (CB1_3_4I1R3CertificateIndex a) (CB1_3_4I1R3P_sound a)
lemma CB1_3_4I1R3Entropy_sound : CB1_3_4I1R3Entropy.Encloses (Foundation.finiteEntropy CB1_3_4I1R3Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_3_4I1R3Value CB1_3_4I1R3Terms CB1_3_4I1R3Terms_sound) (by decide +kernel)
lemma CB1_3_4I1R3Mass_sound : CB1_3_4I1R3Mass.Encloses (∑ a, CB1_3_4I1R3Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_3_4I1R3P CB1_3_4I1R3Value CB1_3_4I1R3P_sound) (by decide +kernel)
lemma CB1_3_4I1R3MassTermLog_sound : CB1_3_4I1R3MassTermLog.Encloses (Real.log ((∑ a, CB1_3_4I1R3Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB1_3_4I1R3Mass_sound) (w := CB1_3_4I1R3MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CB1_3_4I1R3MassTerm_sound : CB1_3_4I1R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_3_4I1R3Value a))) := by
  exact contains_sound (entropyTerm_ball (CB1_3_4I1R3Mass_sound) CB1_3_4I1R3MassTermLog_sound) (by decide +kernel)
lemma CB1_3_4I1R3H_sound : CB1_3_4I1R3H.Encloses (homogeneousEntropy CB1_3_4I1R3Value) := by
  exact contains_sound (homogeneous_enclosed CB1_3_4I1R3Value CB1_3_4I1R3MassTerm_sound CB1_3_4I1R3Entropy_sound) (by decide +kernel)
lemma CB1_3_4I1R4Raw_sound (a : Fin 6) :
    (CB1_3_4I1R4Raw a).Encloses (CB1_3_4I1R4Value a) := by
  exact residualBall_sound_on (below (shape 1 3 4)) B1_3_4Law (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 1 (fun u => B1_3_4Little u ((stageBPriority (shape 1 3 4)) 1)) (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 1) a : ℝ)) (fun u _ => B1_3_4Law_sound u) (fun u _ a => B1_3_4Little_sound u ((stageBPriority (shape 1 3 4)) 1) a) 4 a
lemma CB1_3_4I1R4Certificates_valid :
    CB1_3_4I1R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB1_3_4I1R4P_check : ∀ a : Fin 6, contains (CB1_3_4I1R4Raw a) (CB1_3_4I1R4P a) = true := by
  decide +kernel
lemma CB1_3_4I1R4P_sound (a : Fin 6) :
    (CB1_3_4I1R4P a).Encloses (CB1_3_4I1R4Value a) :=
  contains_sound (CB1_3_4I1R4Raw_sound a) (CB1_3_4I1R4P_check a)
lemma CB1_3_4I1R4Terms_sound (a : Fin 6) :
    (CB1_3_4I1R4Terms a).Encloses (Foundation.entropyTerm (CB1_3_4I1R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_3_4I1R4Certificates_valid
    (CB1_3_4I1R4CertificateIndex a) (CB1_3_4I1R4P_sound a)
lemma CB1_3_4I1R4Entropy_sound : CB1_3_4I1R4Entropy.Encloses (Foundation.finiteEntropy CB1_3_4I1R4Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_3_4I1R4Value CB1_3_4I1R4Terms CB1_3_4I1R4Terms_sound) (by decide +kernel)
lemma CB1_3_4I1R4Mass_sound : CB1_3_4I1R4Mass.Encloses (∑ a, CB1_3_4I1R4Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_3_4I1R4P CB1_3_4I1R4Value CB1_3_4I1R4P_sound) (by decide +kernel)
lemma CB1_3_4I1R4MassTerm_sound : CB1_3_4I1R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_3_4I1R4Value a))) :=
  entropyTerm_zero_ball (CB1_3_4I1R4Mass_sound)
lemma CB1_3_4I1R4H_sound : CB1_3_4I1R4H.Encloses (homogeneousEntropy CB1_3_4I1R4Value) := by
  exact contains_sound (homogeneous_enclosed CB1_3_4I1R4Value CB1_3_4I1R4MassTerm_sound CB1_3_4I1R4Entropy_sound) (by decide +kernel)
lemma CB1_3_4I1R5Raw_sound (a : Fin 6) :
    (CB1_3_4I1R5Raw a).Encloses (CB1_3_4I1R5Value a) := by
  exact residualBall_sound_on (below (shape 1 3 4)) B1_3_4Law (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 1 (fun u => B1_3_4Little u ((stageBPriority (shape 1 3 4)) 1)) (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 1) a : ℝ)) (fun u _ => B1_3_4Law_sound u) (fun u _ a => B1_3_4Little_sound u ((stageBPriority (shape 1 3 4)) 1) a) 5 a
lemma CB1_3_4I1R5Certificates_valid :
    CB1_3_4I1R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB1_3_4I1R5P_check : ∀ a : Fin 6, contains (CB1_3_4I1R5Raw a) (CB1_3_4I1R5P a) = true := by
  decide +kernel
lemma CB1_3_4I1R5P_sound (a : Fin 6) :
    (CB1_3_4I1R5P a).Encloses (CB1_3_4I1R5Value a) :=
  contains_sound (CB1_3_4I1R5Raw_sound a) (CB1_3_4I1R5P_check a)
lemma CB1_3_4I1R5Terms_sound (a : Fin 6) :
    (CB1_3_4I1R5Terms a).Encloses (Foundation.entropyTerm (CB1_3_4I1R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_3_4I1R5Certificates_valid
    (CB1_3_4I1R5CertificateIndex a) (CB1_3_4I1R5P_sound a)
lemma CB1_3_4I1R5Entropy_sound : CB1_3_4I1R5Entropy.Encloses (Foundation.finiteEntropy CB1_3_4I1R5Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_3_4I1R5Value CB1_3_4I1R5Terms CB1_3_4I1R5Terms_sound) (by decide +kernel)
lemma CB1_3_4I1R5Mass_sound : CB1_3_4I1R5Mass.Encloses (∑ a, CB1_3_4I1R5Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_3_4I1R5P CB1_3_4I1R5Value CB1_3_4I1R5P_sound) (by decide +kernel)
lemma CB1_3_4I1R5MassTerm_sound : CB1_3_4I1R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_3_4I1R5Value a))) :=
  entropyTerm_zero_ball (CB1_3_4I1R5Mass_sound)
lemma CB1_3_4I1R5H_sound : CB1_3_4I1R5H.Encloses (homogeneousEntropy CB1_3_4I1R5Value) := by
  exact contains_sound (homogeneous_enclosed CB1_3_4I1R5Value CB1_3_4I1R5MassTerm_sound CB1_3_4I1R5Entropy_sound) (by decide +kernel)
lemma CB1_3_4I1R6Raw_sound (a : Fin 6) :
    (CB1_3_4I1R6Raw a).Encloses (CB1_3_4I1R6Value a) := by
  exact residualBall_sound_on (below (shape 1 3 4)) B1_3_4Law (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 1 (fun u => B1_3_4Little u ((stageBPriority (shape 1 3 4)) 1)) (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 1) a : ℝ)) (fun u _ => B1_3_4Law_sound u) (fun u _ a => B1_3_4Little_sound u ((stageBPriority (shape 1 3 4)) 1) a) 6 a
lemma CB1_3_4I1R6Certificates_valid :
    CB1_3_4I1R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB1_3_4I1R6P_check : ∀ a : Fin 6, contains (CB1_3_4I1R6Raw a) (CB1_3_4I1R6P a) = true := by
  decide +kernel
lemma CB1_3_4I1R6P_sound (a : Fin 6) :
    (CB1_3_4I1R6P a).Encloses (CB1_3_4I1R6Value a) :=
  contains_sound (CB1_3_4I1R6Raw_sound a) (CB1_3_4I1R6P_check a)
lemma CB1_3_4I1R6Terms_sound (a : Fin 6) :
    (CB1_3_4I1R6Terms a).Encloses (Foundation.entropyTerm (CB1_3_4I1R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_3_4I1R6Certificates_valid
    (CB1_3_4I1R6CertificateIndex a) (CB1_3_4I1R6P_sound a)
lemma CB1_3_4I1R6Entropy_sound : CB1_3_4I1R6Entropy.Encloses (Foundation.finiteEntropy CB1_3_4I1R6Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_3_4I1R6Value CB1_3_4I1R6Terms CB1_3_4I1R6Terms_sound) (by decide +kernel)
lemma CB1_3_4I1R6Mass_sound : CB1_3_4I1R6Mass.Encloses (∑ a, CB1_3_4I1R6Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_3_4I1R6P CB1_3_4I1R6Value CB1_3_4I1R6P_sound) (by decide +kernel)
lemma CB1_3_4I1R6MassTerm_sound : CB1_3_4I1R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_3_4I1R6Value a))) :=
  entropyTerm_zero_ball (CB1_3_4I1R6Mass_sound)
lemma CB1_3_4I1R6H_sound : CB1_3_4I1R6H.Encloses (homogeneousEntropy CB1_3_4I1R6Value) := by
  exact contains_sound (homogeneous_enclosed CB1_3_4I1R6Value CB1_3_4I1R6MassTerm_sound CB1_3_4I1R6Entropy_sound) (by decide +kernel)
lemma CB1_3_4I1R7Raw_sound (a : Fin 6) :
    (CB1_3_4I1R7Raw a).Encloses (CB1_3_4I1R7Value a) := by
  exact residualBall_sound_on (below (shape 1 3 4)) B1_3_4Law (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 1 (fun u => B1_3_4Little u ((stageBPriority (shape 1 3 4)) 1)) (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 1) a : ℝ)) (fun u _ => B1_3_4Law_sound u) (fun u _ a => B1_3_4Little_sound u ((stageBPriority (shape 1 3 4)) 1) a) 7 a
lemma CB1_3_4I1R7Certificates_valid :
    CB1_3_4I1R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB1_3_4I1R7P_check : ∀ a : Fin 6, contains (CB1_3_4I1R7Raw a) (CB1_3_4I1R7P a) = true := by
  decide +kernel
lemma CB1_3_4I1R7P_sound (a : Fin 6) :
    (CB1_3_4I1R7P a).Encloses (CB1_3_4I1R7Value a) :=
  contains_sound (CB1_3_4I1R7Raw_sound a) (CB1_3_4I1R7P_check a)
lemma CB1_3_4I1R7Terms_sound (a : Fin 6) :
    (CB1_3_4I1R7Terms a).Encloses (Foundation.entropyTerm (CB1_3_4I1R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_3_4I1R7Certificates_valid
    (CB1_3_4I1R7CertificateIndex a) (CB1_3_4I1R7P_sound a)
lemma CB1_3_4I1R7Entropy_sound : CB1_3_4I1R7Entropy.Encloses (Foundation.finiteEntropy CB1_3_4I1R7Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_3_4I1R7Value CB1_3_4I1R7Terms CB1_3_4I1R7Terms_sound) (by decide +kernel)
lemma CB1_3_4I1R7Mass_sound : CB1_3_4I1R7Mass.Encloses (∑ a, CB1_3_4I1R7Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_3_4I1R7P CB1_3_4I1R7Value CB1_3_4I1R7P_sound) (by decide +kernel)
lemma CB1_3_4I1R7MassTerm_sound : CB1_3_4I1R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_3_4I1R7Value a))) :=
  entropyTerm_zero_ball (CB1_3_4I1R7Mass_sound)
lemma CB1_3_4I1R7H_sound : CB1_3_4I1R7H.Encloses (homogeneousEntropy CB1_3_4I1R7Value) := by
  exact contains_sound (homogeneous_enclosed CB1_3_4I1R7Value CB1_3_4I1R7MassTerm_sound CB1_3_4I1R7Entropy_sound) (by decide +kernel)
lemma CB1_3_4I1R8Raw_sound (a : Fin 6) :
    (CB1_3_4I1R8Raw a).Encloses (CB1_3_4I1R8Value a) := by
  exact residualBall_sound_on (below (shape 1 3 4)) B1_3_4Law (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 1 (fun u => B1_3_4Little u ((stageBPriority (shape 1 3 4)) 1)) (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 1) a : ℝ)) (fun u _ => B1_3_4Law_sound u) (fun u _ a => B1_3_4Little_sound u ((stageBPriority (shape 1 3 4)) 1) a) 8 a
lemma CB1_3_4I1R8Certificates_valid :
    CB1_3_4I1R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB1_3_4I1R8P_check : ∀ a : Fin 6, contains (CB1_3_4I1R8Raw a) (CB1_3_4I1R8P a) = true := by
  decide +kernel
lemma CB1_3_4I1R8P_sound (a : Fin 6) :
    (CB1_3_4I1R8P a).Encloses (CB1_3_4I1R8Value a) :=
  contains_sound (CB1_3_4I1R8Raw_sound a) (CB1_3_4I1R8P_check a)
lemma CB1_3_4I1R8Terms_sound (a : Fin 6) :
    (CB1_3_4I1R8Terms a).Encloses (Foundation.entropyTerm (CB1_3_4I1R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_3_4I1R8Certificates_valid
    (CB1_3_4I1R8CertificateIndex a) (CB1_3_4I1R8P_sound a)
lemma CB1_3_4I1R8Entropy_sound : CB1_3_4I1R8Entropy.Encloses (Foundation.finiteEntropy CB1_3_4I1R8Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_3_4I1R8Value CB1_3_4I1R8Terms CB1_3_4I1R8Terms_sound) (by decide +kernel)
lemma CB1_3_4I1R8Mass_sound : CB1_3_4I1R8Mass.Encloses (∑ a, CB1_3_4I1R8Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_3_4I1R8P CB1_3_4I1R8Value CB1_3_4I1R8P_sound) (by decide +kernel)
lemma CB1_3_4I1R8MassTerm_sound : CB1_3_4I1R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_3_4I1R8Value a))) :=
  entropyTerm_zero_ball (CB1_3_4I1R8Mass_sound)
lemma CB1_3_4I1R8H_sound : CB1_3_4I1R8H.Encloses (homogeneousEntropy CB1_3_4I1R8Value) := by
  exact contains_sound (homogeneous_enclosed CB1_3_4I1R8Value CB1_3_4I1R8MassTerm_sound CB1_3_4I1R8Entropy_sound) (by decide +kernel)
lemma CB1_3_4I1R9Raw_sound (a : Fin 6) :
    (CB1_3_4I1R9Raw a).Encloses (CB1_3_4I1R9Value a) := by
  exact residualBall_sound_on (below (shape 1 3 4)) B1_3_4Law (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 1 (fun u => B1_3_4Little u ((stageBPriority (shape 1 3 4)) 1)) (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 1) a : ℝ)) (fun u _ => B1_3_4Law_sound u) (fun u _ a => B1_3_4Little_sound u ((stageBPriority (shape 1 3 4)) 1) a) 9 a
lemma CB1_3_4I1R9Certificates_valid :
    CB1_3_4I1R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB1_3_4I1R9P_check : ∀ a : Fin 6, contains (CB1_3_4I1R9Raw a) (CB1_3_4I1R9P a) = true := by
  decide +kernel
lemma CB1_3_4I1R9P_sound (a : Fin 6) :
    (CB1_3_4I1R9P a).Encloses (CB1_3_4I1R9Value a) :=
  contains_sound (CB1_3_4I1R9Raw_sound a) (CB1_3_4I1R9P_check a)
lemma CB1_3_4I1R9Terms_sound (a : Fin 6) :
    (CB1_3_4I1R9Terms a).Encloses (Foundation.entropyTerm (CB1_3_4I1R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_3_4I1R9Certificates_valid
    (CB1_3_4I1R9CertificateIndex a) (CB1_3_4I1R9P_sound a)
lemma CB1_3_4I1R9Entropy_sound : CB1_3_4I1R9Entropy.Encloses (Foundation.finiteEntropy CB1_3_4I1R9Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_3_4I1R9Value CB1_3_4I1R9Terms CB1_3_4I1R9Terms_sound) (by decide +kernel)
lemma CB1_3_4I1R9Mass_sound : CB1_3_4I1R9Mass.Encloses (∑ a, CB1_3_4I1R9Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_3_4I1R9P CB1_3_4I1R9Value CB1_3_4I1R9P_sound) (by decide +kernel)
lemma CB1_3_4I1R9MassTerm_sound : CB1_3_4I1R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_3_4I1R9Value a))) :=
  entropyTerm_zero_ball (CB1_3_4I1R9Mass_sound)
lemma CB1_3_4I1R9H_sound : CB1_3_4I1R9H.Encloses (homogeneousEntropy CB1_3_4I1R9Value) := by
  exact contains_sound (homogeneous_enclosed CB1_3_4I1R9Value CB1_3_4I1R9MassTerm_sound CB1_3_4I1R9Entropy_sound) (by decide +kernel)
lemma CB1_3_4I1R10Raw_sound (a : Fin 6) :
    (CB1_3_4I1R10Raw a).Encloses (CB1_3_4I1R10Value a) := by
  exact residualBall_sound_on (below (shape 1 3 4)) B1_3_4Law (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 1 (fun u => B1_3_4Little u ((stageBPriority (shape 1 3 4)) 1)) (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 1) a : ℝ)) (fun u _ => B1_3_4Law_sound u) (fun u _ a => B1_3_4Little_sound u ((stageBPriority (shape 1 3 4)) 1) a) 10 a
lemma CB1_3_4I1R10Certificates_valid :
    CB1_3_4I1R10Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB1_3_4I1R10P_check : ∀ a : Fin 6, contains (CB1_3_4I1R10Raw a) (CB1_3_4I1R10P a) = true := by
  decide +kernel
lemma CB1_3_4I1R10P_sound (a : Fin 6) :
    (CB1_3_4I1R10P a).Encloses (CB1_3_4I1R10Value a) :=
  contains_sound (CB1_3_4I1R10Raw_sound a) (CB1_3_4I1R10P_check a)
lemma CB1_3_4I1R10Terms_sound (a : Fin 6) :
    (CB1_3_4I1R10Terms a).Encloses (Foundation.entropyTerm (CB1_3_4I1R10Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_3_4I1R10Certificates_valid
    (CB1_3_4I1R10CertificateIndex a) (CB1_3_4I1R10P_sound a)
lemma CB1_3_4I1R10Entropy_sound : CB1_3_4I1R10Entropy.Encloses (Foundation.finiteEntropy CB1_3_4I1R10Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_3_4I1R10Value CB1_3_4I1R10Terms CB1_3_4I1R10Terms_sound) (by decide +kernel)
lemma CB1_3_4I1R10Mass_sound : CB1_3_4I1R10Mass.Encloses (∑ a, CB1_3_4I1R10Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_3_4I1R10P CB1_3_4I1R10Value CB1_3_4I1R10P_sound) (by decide +kernel)
lemma CB1_3_4I1R10MassTerm_sound : CB1_3_4I1R10MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_3_4I1R10Value a))) :=
  entropyTerm_zero_ball (CB1_3_4I1R10Mass_sound)
lemma CB1_3_4I1R10H_sound : CB1_3_4I1R10H.Encloses (homogeneousEntropy CB1_3_4I1R10Value) := by
  exact contains_sound (homogeneous_enclosed CB1_3_4I1R10Value CB1_3_4I1R10MassTerm_sound CB1_3_4I1R10Entropy_sound) (by decide +kernel)
lemma CB1_3_4I1R11Raw_sound (a : Fin 6) :
    (CB1_3_4I1R11Raw a).Encloses (CB1_3_4I1R11Value a) := by
  exact residualBall_sound_on (below (shape 1 3 4)) B1_3_4Law (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 1 (fun u => B1_3_4Little u ((stageBPriority (shape 1 3 4)) 1)) (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 1) a : ℝ)) (fun u _ => B1_3_4Law_sound u) (fun u _ a => B1_3_4Little_sound u ((stageBPriority (shape 1 3 4)) 1) a) 11 a
lemma CB1_3_4I1R11Certificates_valid :
    CB1_3_4I1R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB1_3_4I1R11P_check : ∀ a : Fin 6, contains (CB1_3_4I1R11Raw a) (CB1_3_4I1R11P a) = true := by
  decide +kernel
lemma CB1_3_4I1R11P_sound (a : Fin 6) :
    (CB1_3_4I1R11P a).Encloses (CB1_3_4I1R11Value a) :=
  contains_sound (CB1_3_4I1R11Raw_sound a) (CB1_3_4I1R11P_check a)
lemma CB1_3_4I1R11Terms_sound (a : Fin 6) :
    (CB1_3_4I1R11Terms a).Encloses (Foundation.entropyTerm (CB1_3_4I1R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_3_4I1R11Certificates_valid
    (CB1_3_4I1R11CertificateIndex a) (CB1_3_4I1R11P_sound a)
lemma CB1_3_4I1R11Entropy_sound : CB1_3_4I1R11Entropy.Encloses (Foundation.finiteEntropy CB1_3_4I1R11Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_3_4I1R11Value CB1_3_4I1R11Terms CB1_3_4I1R11Terms_sound) (by decide +kernel)
lemma CB1_3_4I1R11Mass_sound : CB1_3_4I1R11Mass.Encloses (∑ a, CB1_3_4I1R11Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_3_4I1R11P CB1_3_4I1R11Value CB1_3_4I1R11P_sound) (by decide +kernel)
lemma CB1_3_4I1R11MassTerm_sound : CB1_3_4I1R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_3_4I1R11Value a))) :=
  entropyTerm_zero_ball (CB1_3_4I1R11Mass_sound)
lemma CB1_3_4I1R11H_sound : CB1_3_4I1R11H.Encloses (homogeneousEntropy CB1_3_4I1R11Value) := by
  exact contains_sound (homogeneous_enclosed CB1_3_4I1R11Value CB1_3_4I1R11MassTerm_sound CB1_3_4I1R11Entropy_sound) (by decide +kernel)
lemma CB1_3_4I1R12Raw_sound (a : Fin 6) :
    (CB1_3_4I1R12Raw a).Encloses (CB1_3_4I1R12Value a) := by
  exact residualBall_sound_on (below (shape 1 3 4)) B1_3_4Law (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 1 (fun u => B1_3_4Little u ((stageBPriority (shape 1 3 4)) 1)) (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 1) a : ℝ)) (fun u _ => B1_3_4Law_sound u) (fun u _ a => B1_3_4Little_sound u ((stageBPriority (shape 1 3 4)) 1) a) 12 a
lemma CB1_3_4I1R12Certificates_valid :
    CB1_3_4I1R12Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB1_3_4I1R12P_check : ∀ a : Fin 6, contains (CB1_3_4I1R12Raw a) (CB1_3_4I1R12P a) = true := by
  decide +kernel
lemma CB1_3_4I1R12P_sound (a : Fin 6) :
    (CB1_3_4I1R12P a).Encloses (CB1_3_4I1R12Value a) :=
  contains_sound (CB1_3_4I1R12Raw_sound a) (CB1_3_4I1R12P_check a)
lemma CB1_3_4I1R12Terms_sound (a : Fin 6) :
    (CB1_3_4I1R12Terms a).Encloses (Foundation.entropyTerm (CB1_3_4I1R12Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_3_4I1R12Certificates_valid
    (CB1_3_4I1R12CertificateIndex a) (CB1_3_4I1R12P_sound a)
lemma CB1_3_4I1R12Entropy_sound : CB1_3_4I1R12Entropy.Encloses (Foundation.finiteEntropy CB1_3_4I1R12Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_3_4I1R12Value CB1_3_4I1R12Terms CB1_3_4I1R12Terms_sound) (by decide +kernel)
lemma CB1_3_4I1R12Mass_sound : CB1_3_4I1R12Mass.Encloses (∑ a, CB1_3_4I1R12Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_3_4I1R12P CB1_3_4I1R12Value CB1_3_4I1R12P_sound) (by decide +kernel)
lemma CB1_3_4I1R12MassTerm_sound : CB1_3_4I1R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_3_4I1R12Value a))) :=
  entropyTerm_zero_ball (CB1_3_4I1R12Mass_sound)
lemma CB1_3_4I1R12H_sound : CB1_3_4I1R12H.Encloses (homogeneousEntropy CB1_3_4I1R12Value) := by
  exact contains_sound (homogeneous_enclosed CB1_3_4I1R12Value CB1_3_4I1R12MassTerm_sound CB1_3_4I1R12Entropy_sound) (by decide +kernel)
lemma CB1_3_4I1R13Raw_sound (a : Fin 6) :
    (CB1_3_4I1R13Raw a).Encloses (CB1_3_4I1R13Value a) := by
  exact residualBall_sound_on (below (shape 1 3 4)) B1_3_4Law (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 1 (fun u => B1_3_4Little u ((stageBPriority (shape 1 3 4)) 1)) (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 1) a : ℝ)) (fun u _ => B1_3_4Law_sound u) (fun u _ a => B1_3_4Little_sound u ((stageBPriority (shape 1 3 4)) 1) a) 13 a
lemma CB1_3_4I1R13Certificates_valid :
    CB1_3_4I1R13Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB1_3_4I1R13P_check : ∀ a : Fin 6, contains (CB1_3_4I1R13Raw a) (CB1_3_4I1R13P a) = true := by
  decide +kernel
lemma CB1_3_4I1R13P_sound (a : Fin 6) :
    (CB1_3_4I1R13P a).Encloses (CB1_3_4I1R13Value a) :=
  contains_sound (CB1_3_4I1R13Raw_sound a) (CB1_3_4I1R13P_check a)
lemma CB1_3_4I1R13Terms_sound (a : Fin 6) :
    (CB1_3_4I1R13Terms a).Encloses (Foundation.entropyTerm (CB1_3_4I1R13Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_3_4I1R13Certificates_valid
    (CB1_3_4I1R13CertificateIndex a) (CB1_3_4I1R13P_sound a)
lemma CB1_3_4I1R13Entropy_sound : CB1_3_4I1R13Entropy.Encloses (Foundation.finiteEntropy CB1_3_4I1R13Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_3_4I1R13Value CB1_3_4I1R13Terms CB1_3_4I1R13Terms_sound) (by decide +kernel)
lemma CB1_3_4I1R13Mass_sound : CB1_3_4I1R13Mass.Encloses (∑ a, CB1_3_4I1R13Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_3_4I1R13P CB1_3_4I1R13Value CB1_3_4I1R13P_sound) (by decide +kernel)
lemma CB1_3_4I1R13MassTerm_sound : CB1_3_4I1R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_3_4I1R13Value a))) :=
  entropyTerm_zero_ball (CB1_3_4I1R13Mass_sound)
lemma CB1_3_4I1R13H_sound : CB1_3_4I1R13H.Encloses (homogeneousEntropy CB1_3_4I1R13Value) := by
  exact contains_sound (homogeneous_enclosed CB1_3_4I1R13Value CB1_3_4I1R13MassTerm_sound CB1_3_4I1R13Entropy_sound) (by decide +kernel)
lemma CB1_3_4I1R14Raw_sound (a : Fin 6) :
    (CB1_3_4I1R14Raw a).Encloses (CB1_3_4I1R14Value a) := by
  exact residualBall_sound_on (below (shape 1 3 4)) B1_3_4Law (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 1 (fun u => B1_3_4Little u ((stageBPriority (shape 1 3 4)) 1)) (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 1) a : ℝ)) (fun u _ => B1_3_4Law_sound u) (fun u _ a => B1_3_4Little_sound u ((stageBPriority (shape 1 3 4)) 1) a) 14 a
lemma CB1_3_4I1R14Certificates_valid :
    CB1_3_4I1R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB1_3_4I1R14P_check : ∀ a : Fin 6, contains (CB1_3_4I1R14Raw a) (CB1_3_4I1R14P a) = true := by
  decide +kernel
lemma CB1_3_4I1R14P_sound (a : Fin 6) :
    (CB1_3_4I1R14P a).Encloses (CB1_3_4I1R14Value a) :=
  contains_sound (CB1_3_4I1R14Raw_sound a) (CB1_3_4I1R14P_check a)
lemma CB1_3_4I1R14Terms_sound (a : Fin 6) :
    (CB1_3_4I1R14Terms a).Encloses (Foundation.entropyTerm (CB1_3_4I1R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_3_4I1R14Certificates_valid
    (CB1_3_4I1R14CertificateIndex a) (CB1_3_4I1R14P_sound a)
lemma CB1_3_4I1R14Entropy_sound : CB1_3_4I1R14Entropy.Encloses (Foundation.finiteEntropy CB1_3_4I1R14Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_3_4I1R14Value CB1_3_4I1R14Terms CB1_3_4I1R14Terms_sound) (by decide +kernel)
lemma CB1_3_4I1R14Mass_sound : CB1_3_4I1R14Mass.Encloses (∑ a, CB1_3_4I1R14Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_3_4I1R14P CB1_3_4I1R14Value CB1_3_4I1R14P_sound) (by decide +kernel)
lemma CB1_3_4I1R14MassTerm_sound : CB1_3_4I1R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_3_4I1R14Value a))) :=
  entropyTerm_zero_ball (CB1_3_4I1R14Mass_sound)
lemma CB1_3_4I1R14H_sound : CB1_3_4I1R14H.Encloses (homogeneousEntropy CB1_3_4I1R14Value) := by
  exact contains_sound (homogeneous_enclosed CB1_3_4I1R14Value CB1_3_4I1R14MassTerm_sound CB1_3_4I1R14Entropy_sound) (by decide +kernel)
lemma CB1_3_4I1R15Raw_sound (a : Fin 6) :
    (CB1_3_4I1R15Raw a).Encloses (CB1_3_4I1R15Value a) := by
  exact residualBall_sound_on (below (shape 1 3 4)) B1_3_4Law (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 1 (fun u => B1_3_4Little u ((stageBPriority (shape 1 3 4)) 1)) (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 1) a : ℝ)) (fun u _ => B1_3_4Law_sound u) (fun u _ a => B1_3_4Little_sound u ((stageBPriority (shape 1 3 4)) 1) a) 15 a
lemma CB1_3_4I1R15Certificates_valid :
    CB1_3_4I1R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB1_3_4I1R15P_check : ∀ a : Fin 6, contains (CB1_3_4I1R15Raw a) (CB1_3_4I1R15P a) = true := by
  decide +kernel
lemma CB1_3_4I1R15P_sound (a : Fin 6) :
    (CB1_3_4I1R15P a).Encloses (CB1_3_4I1R15Value a) :=
  contains_sound (CB1_3_4I1R15Raw_sound a) (CB1_3_4I1R15P_check a)
lemma CB1_3_4I1R15Terms_sound (a : Fin 6) :
    (CB1_3_4I1R15Terms a).Encloses (Foundation.entropyTerm (CB1_3_4I1R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_3_4I1R15Certificates_valid
    (CB1_3_4I1R15CertificateIndex a) (CB1_3_4I1R15P_sound a)
lemma CB1_3_4I1R15Entropy_sound : CB1_3_4I1R15Entropy.Encloses (Foundation.finiteEntropy CB1_3_4I1R15Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_3_4I1R15Value CB1_3_4I1R15Terms CB1_3_4I1R15Terms_sound) (by decide +kernel)
lemma CB1_3_4I1R15Mass_sound : CB1_3_4I1R15Mass.Encloses (∑ a, CB1_3_4I1R15Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_3_4I1R15P CB1_3_4I1R15Value CB1_3_4I1R15P_sound) (by decide +kernel)
lemma CB1_3_4I1R15MassTerm_sound : CB1_3_4I1R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_3_4I1R15Value a))) :=
  entropyTerm_zero_ball (CB1_3_4I1R15Mass_sound)
lemma CB1_3_4I1R15H_sound : CB1_3_4I1R15H.Encloses (homogeneousEntropy CB1_3_4I1R15Value) := by
  exact contains_sound (homogeneous_enclosed CB1_3_4I1R15Value CB1_3_4I1R15MassTerm_sound CB1_3_4I1R15Entropy_sound) (by decide +kernel)
lemma CB1_3_4I1R16Raw_sound (a : Fin 6) :
    (CB1_3_4I1R16Raw a).Encloses (CB1_3_4I1R16Value a) := by
  exact residualBall_sound_on (below (shape 1 3 4)) B1_3_4Law (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 1 (fun u => B1_3_4Little u ((stageBPriority (shape 1 3 4)) 1)) (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 1) a : ℝ)) (fun u _ => B1_3_4Law_sound u) (fun u _ a => B1_3_4Little_sound u ((stageBPriority (shape 1 3 4)) 1) a) 16 a
lemma CB1_3_4I1R16Certificates_valid :
    CB1_3_4I1R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB1_3_4I1R16P_check : ∀ a : Fin 6, contains (CB1_3_4I1R16Raw a) (CB1_3_4I1R16P a) = true := by
  decide +kernel
lemma CB1_3_4I1R16P_sound (a : Fin 6) :
    (CB1_3_4I1R16P a).Encloses (CB1_3_4I1R16Value a) :=
  contains_sound (CB1_3_4I1R16Raw_sound a) (CB1_3_4I1R16P_check a)
lemma CB1_3_4I1R16Terms_sound (a : Fin 6) :
    (CB1_3_4I1R16Terms a).Encloses (Foundation.entropyTerm (CB1_3_4I1R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_3_4I1R16Certificates_valid
    (CB1_3_4I1R16CertificateIndex a) (CB1_3_4I1R16P_sound a)
lemma CB1_3_4I1R16Entropy_sound : CB1_3_4I1R16Entropy.Encloses (Foundation.finiteEntropy CB1_3_4I1R16Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_3_4I1R16Value CB1_3_4I1R16Terms CB1_3_4I1R16Terms_sound) (by decide +kernel)
lemma CB1_3_4I1R16Mass_sound : CB1_3_4I1R16Mass.Encloses (∑ a, CB1_3_4I1R16Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_3_4I1R16P CB1_3_4I1R16Value CB1_3_4I1R16P_sound) (by decide +kernel)
lemma CB1_3_4I1R16MassTerm_sound : CB1_3_4I1R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_3_4I1R16Value a))) :=
  entropyTerm_zero_ball (CB1_3_4I1R16Mass_sound)
lemma CB1_3_4I1R16H_sound : CB1_3_4I1R16H.Encloses (homogeneousEntropy CB1_3_4I1R16Value) := by
  exact contains_sound (homogeneous_enclosed CB1_3_4I1R16Value CB1_3_4I1R16MassTerm_sound CB1_3_4I1R16Entropy_sound) (by decide +kernel)
lemma CB1_3_4I1ResidualEntropies_sound (k : Fin 17) :
    (CB1_3_4I1ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 1 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 1) a : ℝ)) k)) := by
  fin_cases k
  · exact CB1_3_4I1R0H_sound
  · exact CB1_3_4I1R1H_sound
  · exact CB1_3_4I1R2H_sound
  · exact CB1_3_4I1R3H_sound
  · exact CB1_3_4I1R4H_sound
  · exact CB1_3_4I1R5H_sound
  · exact CB1_3_4I1R6H_sound
  · exact CB1_3_4I1R7H_sound
  · exact CB1_3_4I1R8H_sound
  · exact CB1_3_4I1R9H_sound
  · exact CB1_3_4I1R10H_sound
  · exact CB1_3_4I1R11H_sound
  · exact CB1_3_4I1R12H_sound
  · exact CB1_3_4I1R13H_sound
  · exact CB1_3_4I1R14H_sound
  · exact CB1_3_4I1R15H_sound
  · exact CB1_3_4I1R16H_sound
lemma CB1_3_4I1S1_3_0E_4Log_sound : CB1_3_4I1S1_3_0E_4Log.Encloses (Real.log (CB1_3_4I1S1_3_0Value (4 : Fin 6))) := by
  exact log_exact_one_ball ((B1_3_4Little_sound (shape 1 3 0) ((stageBPriority (shape 1 3 4)) 1)) (4 : Fin 6))
lemma CB1_3_4I1S1_3_0E_4_sound : CB1_3_4I1S1_3_0E_4.Encloses (Foundation.entropyTerm (CB1_3_4I1S1_3_0Value (4 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B1_3_4Little_sound (shape 1 3 0) ((stageBPriority (shape 1 3 4)) 1)) (4 : Fin 6)) CB1_3_4I1S1_3_0E_4Log_sound) (by decide +kernel)
lemma CB1_3_4I1S1_3_0Terms_sound (a : Fin 6) :
    (CB1_3_4I1S1_3_0Terms a).Encloses (Foundation.entropyTerm (CB1_3_4I1S1_3_0Value a)) := by
  fin_cases a
  · exact (entropyTerm_zero_ball ((B1_3_4Little_sound (shape 1 3 0) ((stageBPriority (shape 1 3 4)) 1)) (0 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B1_3_4Little_sound (shape 1 3 0) ((stageBPriority (shape 1 3 4)) 1)) (1 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B1_3_4Little_sound (shape 1 3 0) ((stageBPriority (shape 1 3 4)) 1)) (2 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B1_3_4Little_sound (shape 1 3 0) ((stageBPriority (shape 1 3 4)) 1)) (3 : Fin 6)))
  · exact CB1_3_4I1S1_3_0E_4_sound
  · exact (entropyTerm_zero_ball ((B1_3_4Little_sound (shape 1 3 0) ((stageBPriority (shape 1 3 4)) 1)) (5 : Fin 6)))
lemma CB1_3_4I1S1_3_0Entropy_sound : CB1_3_4I1S1_3_0Entropy.Encloses (Foundation.finiteEntropy CB1_3_4I1S1_3_0Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_3_4I1S1_3_0Value CB1_3_4I1S1_3_0Terms CB1_3_4I1S1_3_0Terms_sound) (by decide +kernel)
lemma CB1_3_4I1S1_3_0Mass_sound : CB1_3_4I1S1_3_0Mass.Encloses (∑ a, CB1_3_4I1S1_3_0Value a) := by
  exact contains_sound (finSumBall_sound 6 (B1_3_4Little (shape 1 3 0) ((stageBPriority (shape 1 3 4)) 1)) CB1_3_4I1S1_3_0Value (B1_3_4Little_sound (shape 1 3 0) ((stageBPriority (shape 1 3 4)) 1))) (by decide +kernel)
lemma CB1_3_4I1S1_3_0MassTermLog_sound : CB1_3_4I1S1_3_0MassTermLog.Encloses (Real.log ((∑ a, CB1_3_4I1S1_3_0Value a))) := by
  exact log_exact_one_ball (CB1_3_4I1S1_3_0Mass_sound)
lemma CB1_3_4I1S1_3_0MassTerm_sound : CB1_3_4I1S1_3_0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_3_4I1S1_3_0Value a))) := by
  exact contains_sound (entropyTerm_ball (CB1_3_4I1S1_3_0Mass_sound) CB1_3_4I1S1_3_0MassTermLog_sound) (by decide +kernel)
lemma CB1_3_4I1S1_3_0H_sound : CB1_3_4I1S1_3_0H.Encloses (homogeneousEntropy CB1_3_4I1S1_3_0Value) := by
  exact contains_sound (homogeneous_enclosed CB1_3_4I1S1_3_0Value CB1_3_4I1S1_3_0MassTerm_sound CB1_3_4I1S1_3_0Entropy_sound) (by decide +kernel)
lemma CB1_3_4I1Singles_sound (u : Shape) (hu : u ∈ below (shape 1 3 4))
    (hd : designated (stageBPriority (shape 1 3 4)) 1 u) :
    (CB1_3_4I1Singles u).Encloses (homogeneousEntropy ((fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 1) a : ℝ)) u)) := by
  rw [B1_3_4_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (show ¬ designated (stageBPriority (shape 1 3 4)) 1 (shape 0 0 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (stageBPriority (shape 1 3 4)) 1 (shape 0 1 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (stageBPriority (shape 1 3 4)) 1 (shape 0 2 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (stageBPriority (shape 1 3 4)) 1 (shape 0 3 1) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (stageBPriority (shape 1 3 4)) 1 (shape 1 0 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (stageBPriority (shape 1 3 4)) 1 (shape 1 1 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (stageBPriority (shape 1 3 4)) 1 (shape 1 2 1) by decide +kernel) hd |>.elim
  · exact CB1_3_4I1S1_3_0H_sound
lemma CB1_3_4I1Singleton_sound : CB1_3_4I1Singleton.Encloses
    (singletonEntropy (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 1 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 1) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 1 3 4)) B1_3_4Law (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 1
    CB1_3_4I1Singles (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 1) a : ℝ)) (fun u _ => B1_3_4Law_sound u) CB1_3_4I1Singles_sound) (by decide +kernel)
lemma CB1_3_4I1Group_sound : CB1_3_4I1Group.Encloses
    (groupedEntropy (below (shape 1 3 4)) (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (stageBPriority (shape 1 3 4)) 1 (fun u a => (littleLaw (shape 1 3 4) u ((stageBPriority (shape 1 3 4)) 1) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CB1_3_4I1Singleton_sound
    (finSumBall_sound 17 CB1_3_4I1ResidualEntropies _ CB1_3_4I1ResidualEntropies_sound)) (by decide +kernel)

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
lemma CB1_3_4I1_sound_oai : CB1_3_4I1H.Encloses (stageBCapacity (shape 1 3 4) 1) := by
  have hb := contains_sound (Ball.add_sound CB1_3_4I1PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CB1_3_4I1Group_sound)))
    (show contains (.add CB1_3_4I1PairH (.neg (.mul (.exact 2) CB1_3_4I1Group))) CB1_3_4I1H = true by decide +kernel)
  unfold CB1_3_4I1PairValue at hb
  simpa only [stageBCapacity, nativeCapacity,
    show (1 : Fin 3) ≠ 0 by decide, ite_false, if_false, sub_eq_add_neg] using hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB1_3_4I1_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB1_3_4I1_sound_oai
