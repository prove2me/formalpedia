-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_2_13I2_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T14:54:32.48521+00:00
-- url     : https://prove2.me/submissions/ddc1ef1c-9303-48ea-8191-12a8f260326d

import Mathlib
import Definitions.Def_OAIQ254M007
import Definitions.Def_OAIQ254M011
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_mul_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_A1_2_13Law_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_2_13I2PairH_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_2_13I2ResidualEntropies_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_Z0_0_8H2H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_Z0_1_7H2Entropy_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_Z0_2_6H2H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_Z1_0_7H2H_sound
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

theorem ofBounds_sound {lo hi : ℚ} {x : ℝ}
    (hlo : (lo : ℝ) ≤ x) (hhi : x ≤ (hi : ℝ)) :
    (ofBounds lo hi).Encloses x := by
  simp only [Encloses, ofBounds, Rat.cast_add, Rat.cast_div, Rat.cast_ofNat,
    Rat.cast_sub]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

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

theorem inv_sound {a : Ball} {x : ℝ} (hx : a.Encloses x)
    (hpos : 0 < a.lower) : (inv a).Encloses x⁻¹ := by
  have hlo : (0 : ℝ) < a.lower := by exact_mod_cast hpos
  obtain ⟨hl, hu⟩ := bounds hx
  have hxp : 0 < x := lt_of_lt_of_le hlo hl
  apply ofBounds_sound
  · simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_inv, one_div] using
      one_div_le_one_div_of_le hxp hu
  · simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_inv, one_div] using
      one_div_le_one_div_of_le hlo hl

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

lemma list_cast_enclosed {A : Type*} (xs : List A) (b : A → Ball) (v : A → ℚ)
    (h : ∀ a ∈ xs, (b a).Encloses (v a : ℝ)) :
    (listSumBall xs b).Encloses ((xs.map v).sum : ℝ) := by
  simpa only [Rat.cast_list_sum, List.map_map, Function.comp_def] using
    listSumBall_sound xs b (fun a => (v a : ℝ)) h

lemma product_fin6_enclosed (bs : Fin 6 → Fin 6 → Ball) (v : PairSlot → ℝ)
    (h : ∀ i j, (bs i j).Encloses (v (i,j))) :
    (finSumBall 6 (fun i => finSumBall 6 (bs i))).Encloses (∑ s : PairSlot, v s) := by
  rw [Fintype.sum_prod_type]
  exact finSumBall_sound 6 _ _ (fun i => finSumBall_sound 6 _ _ (h i))

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

lemma forall_fin6 {P : Fin 6 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2)
    (h3 : P 3) (h4 : P 4) (h5 : P 5) : ∀ i, P i := by
  intro i
  fin_cases i <;> assumption

lemma pairSumBall_sound (bs : PairSlot → Ball) (v : PairSlot → ℝ)
    (h : ∀ a, (bs a).Encloses (v a)) :
    (pairSumBall bs).Encloses (∑ a, v a) := by
  exact product_fin6_enclosed _ _ (fun i j => h (i,j))

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
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Zero0_1_7
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
lemma w195_sound : w195.Encloses (weight 0 : ℝ) := by
  have he : weight 0 = 1 := by decide +kernel
  rw [he, Rat.cast_one]
  simpa only [w195, Rat.cast_one] using Ball.exact_sound 1

end MatrixMultiplication.NativeNumerics

namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
lemma Z0_1_7Raw_sound_0 (j : Fin 6) :
    (Z0_1_7Raw (0,j)).Encloses (weight (orderedPairInteger (shape 0 1 7) 0 j) : ℝ) := by
  fin_cases j
  · change (Z0_1_7Raw (0,0)).Encloses (weight (orderedPairInteger (shape 0 1 7) 0 0) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 0 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (0,1)).Encloses (weight (orderedPairInteger (shape 0 1 7) 0 1) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 0 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (0,2)).Encloses (weight (orderedPairInteger (shape 0 1 7) 0 2) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 0 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (0,3)).Encloses (weight (orderedPairInteger (shape 0 1 7) 0 3) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 0 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (0,4)).Encloses (weight (orderedPairInteger (shape 0 1 7) 0 4) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 0 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (0,5)).Encloses (weight (orderedPairInteger (shape 0 1 7) 0 5) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 0 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_1_7Raw_sound_1 (j : Fin 6) :
    (Z0_1_7Raw (1,j)).Encloses (weight (orderedPairInteger (shape 0 1 7) 1 j) : ℝ) := by
  fin_cases j
  · change (Z0_1_7Raw (1,0)).Encloses (weight (orderedPairInteger (shape 0 1 7) 1 0) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 1 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (1,1)).Encloses (weight (orderedPairInteger (shape 0 1 7) 1 1) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 1 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (1,2)).Encloses (weight (orderedPairInteger (shape 0 1 7) 1 2) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 1 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (1,3)).Encloses (weight (orderedPairInteger (shape 0 1 7) 1 3) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 1 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (1,4)).Encloses (weight (orderedPairInteger (shape 0 1 7) 1 4) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 1 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (1,5)).Encloses (weight (orderedPairInteger (shape 0 1 7) 1 5) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 1 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_1_7Raw_sound_2 (j : Fin 6) :
    (Z0_1_7Raw (2,j)).Encloses (weight (orderedPairInteger (shape 0 1 7) 2 j) : ℝ) := by
  fin_cases j
  · change (Z0_1_7Raw (2,0)).Encloses (weight (orderedPairInteger (shape 0 1 7) 2 0) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 2 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (2,1)).Encloses (weight (orderedPairInteger (shape 0 1 7) 2 1) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 2 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (2,2)).Encloses (weight (orderedPairInteger (shape 0 1 7) 2 2) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 2 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (2,3)).Encloses (weight (orderedPairInteger (shape 0 1 7) 2 3) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 2 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (2,4)).Encloses (weight (orderedPairInteger (shape 0 1 7) 2 4) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 2 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (2,5)).Encloses (weight (orderedPairInteger (shape 0 1 7) 2 5) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 2 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_1_7Raw_sound_3 (j : Fin 6) :
    (Z0_1_7Raw (3,j)).Encloses (weight (orderedPairInteger (shape 0 1 7) 3 j) : ℝ) := by
  fin_cases j
  · change (Z0_1_7Raw (3,0)).Encloses (weight (orderedPairInteger (shape 0 1 7) 3 0) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 3 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (3,1)).Encloses (weight (orderedPairInteger (shape 0 1 7) 3 1) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 3 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (3,2)).Encloses (weight (orderedPairInteger (shape 0 1 7) 3 2) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 3 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (3,3)).Encloses (weight (orderedPairInteger (shape 0 1 7) 3 3) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 3 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (3,4)).Encloses (weight (orderedPairInteger (shape 0 1 7) 3 4) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 3 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (3,5)).Encloses (weight (orderedPairInteger (shape 0 1 7) 3 5) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 3 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_1_7Raw_sound_4 (j : Fin 6) :
    (Z0_1_7Raw (4,j)).Encloses (weight (orderedPairInteger (shape 0 1 7) 4 j) : ℝ) := by
  fin_cases j
  · change (Z0_1_7Raw (4,0)).Encloses (weight (orderedPairInteger (shape 0 1 7) 4 0) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 4 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (4,1)).Encloses (weight (orderedPairInteger (shape 0 1 7) 4 1) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 4 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (4,2)).Encloses (weight (orderedPairInteger (shape 0 1 7) 4 2) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 4 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (4,3)).Encloses (weight (orderedPairInteger (shape 0 1 7) 4 3) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 4 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (4,4)).Encloses (weight (orderedPairInteger (shape 0 1 7) 4 4) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 4 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (4,5)).Encloses (weight (orderedPairInteger (shape 0 1 7) 4 5) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 4 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_1_7Raw_sound_5 (j : Fin 6) :
    (Z0_1_7Raw (5,j)).Encloses (weight (orderedPairInteger (shape 0 1 7) 5 j) : ℝ) := by
  fin_cases j
  · change (Z0_1_7Raw (5,0)).Encloses (weight (orderedPairInteger (shape 0 1 7) 5 0) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 5 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (5,1)).Encloses (weight (orderedPairInteger (shape 0 1 7) 5 1) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 5 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (5,2)).Encloses (weight (orderedPairInteger (shape 0 1 7) 5 2) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 5 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (5,3)).Encloses (weight (orderedPairInteger (shape 0 1 7) 5 3) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 5 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (5,4)).Encloses (weight (orderedPairInteger (shape 0 1 7) 5 4) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 5 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (5,5)).Encloses (weight (orderedPairInteger (shape 0 1 7) 5 5) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 5 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_1_7Raw_sound (ij : PairSlot) :
    (Z0_1_7Raw ij).Encloses (weight (orderedPairInteger (shape 0 1 7) ij.1 ij.2) : ℝ) := by
  rcases ij with ⟨i,j⟩
  revert i
  exact forall_fin6 (Z0_1_7Raw_sound_0 j) (Z0_1_7Raw_sound_1 j) (Z0_1_7Raw_sound_2 j) (Z0_1_7Raw_sound_3 j) (Z0_1_7Raw_sound_4 j) (Z0_1_7Raw_sound_5 j)
lemma Z0_1_7Den_sound : Z0_1_7Den.Encloses
    (((orderedPairs (shape 0 1 7)).map (fun ij => weight (orderedPairInteger (shape 0 1 7) ij.1 ij.2))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (orderedPairs (shape 0 1 7)) Z0_1_7Raw
    (fun ij => weight (orderedPairInteger (shape 0 1 7) ij.1 ij.2))
    (fun ij _ => Z0_1_7Raw_sound ij)) (by decide +kernel)
lemma Z0_1_7Den_pos : 0 < Z0_1_7Den.lower := by decide +kernel
lemma Z0_1_7Contains : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j = shapeMax (shape 0 1 7) →
    contains (.mul (Z0_1_7Raw (i,j)) (.inv Z0_1_7Den)) (Z0_1_7Probs (i,j)) = true := by
  decide +kernel
lemma Z0_1_7Zero : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j ≠ shapeMax (shape 0 1 7) → Z0_1_7Probs (i,j) = .exact 0 := by
  decide +kernel
lemma Z0_1_7Probs_sound (ij : PairSlot) :
    (Z0_1_7Probs ij).Encloses (zeroPairLaw (shape 0 1 7) ij.1 ij.2 : ℝ) := by
  by_cases h : statisticWeight ij.1 + statisticWeight ij.2 = shapeMax (shape 0 1 7)
  · have hb := contains_sound (Ball.mul_sound (Z0_1_7Raw_sound ij)
      (Ball.inv_sound Z0_1_7Den_sound Z0_1_7Den_pos)) (Z0_1_7Contains ij.1 ij.2 h)
    simpa only [zeroPairLaw, h, ite_true, if_true, Rat.cast_div, Rat.cast_mul,
      Rat.cast_inv, div_eq_mul_inv] using hb
  · rw [Z0_1_7Zero ij.1 ij.2 h]
    simpa only [zeroPairLaw, h, ite_false, if_false] using Ball.exact_sound 0

lemma Z0_1_7Half_sound (w : Fin 3) (ij : PairSlot) :
    (Z0_1_7Half w ij).Encloses (halfLaw (shape 0 1 7) w ij : ℝ) := by
  have hp : positive (shape 0 1 7) = false := by decide +kernel
  simp only [Z0_1_7Half, halfLaw, hp, Bool.false_eq_true, ite_false, if_false]
  split_ifs
  · exact Ball.exact_sound 1
  · exact Ball.exact_sound 0
  · exact Z0_1_7Probs_sound _
  · exact Z0_1_7Probs_sound _

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitB2_3_3
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

lemma A1_2_13_below : below (shape 1 2 13) = [
  (shape 0 0 8),
  (shape 0 1 7),
  (shape 0 2 6),
  (shape 1 0 7),
  (shape 1 1 6),
  (shape 1 2 5)] := by decide +kernel

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Four0_1_7
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
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
lemma Z0_1_7H2Mass_sound : Z0_1_7H2Mass.Encloses (∑ a, Z0_1_7H2Value a) := by
  exact contains_sound (pairSumBall_sound (Z0_1_7Half 2) Z0_1_7H2Value (Z0_1_7Half_sound 2)) (by decide +kernel)
lemma Z0_1_7H2MassTermLog_sound : Z0_1_7H2MassTermLog.Encloses (Real.log ((∑ a, Z0_1_7H2Value a))) := by
  exact log_exact_one_ball (Z0_1_7H2Mass_sound)
lemma Z0_1_7H2MassTerm_sound : Z0_1_7H2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, Z0_1_7H2Value a))) := by
  exact contains_sound (entropyTerm_ball (Z0_1_7H2Mass_sound) Z0_1_7H2MassTermLog_sound) (by decide +kernel)
lemma Z0_1_7H2H_sound : Z0_1_7H2H.Encloses (homogeneousEntropy Z0_1_7H2Value) := by
  exact contains_sound (homogeneous_enclosed Z0_1_7H2Value Z0_1_7H2MassTerm_sound Z0_1_7H2Entropy_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_2_13I2
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
lemma CA1_2_13I2Singles_sound (u : Shape) (hu : u ∈ below (shape 1 2 13))
    (hd : designated (Equiv.refl (Fin 3)) 2 u) :
    (CA1_2_13I2Singles u).Encloses (homogeneousEntropy ((fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) u)) := by
  rw [A1_2_13_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Z0_0_8H2H_sound
  · exact Z0_1_7H2H_sound
  · exact Z0_2_6H2H_sound
  · exact Z1_0_7H2H_sound
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 1 6) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 2 5) by decide +kernel) hd |>.elim
lemma CA1_2_13I2Singleton_sound : CA1_2_13I2Singleton.Encloses
    (singletonEntropy (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 1 2 13)) A1_2_13Law (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2
    CA1_2_13I2Singles (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_2_13Law_sound u) CA1_2_13I2Singles_sound) (by decide +kernel)
lemma CA1_2_13I2Group_sound : CA1_2_13I2Group.Encloses
    (groupedEntropy (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CA1_2_13I2Singleton_sound
    (finSumBall_sound 17 CA1_2_13I2ResidualEntropies _ CA1_2_13I2ResidualEntropies_sound)) (by decide +kernel)

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
lemma CA1_2_13I2_sound_oai : CA1_2_13I2H.Encloses (stageACapacity (shape 1 2 13) 2) := by
  have hb := contains_sound (Ball.add_sound CA1_2_13I2PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CA1_2_13I2Group_sound)))
    (show contains (.add CA1_2_13I2PairH (.neg (.mul (.exact 2) CA1_2_13I2Group))) CA1_2_13I2H = true by decide +kernel)
  unfold CA1_2_13I2PairValue at hb
  simpa only [stageACapacity, nativeCapacity,
    show (2 : Fin 3) ≠ 0 by decide, ite_false, if_false, sub_eq_add_neg] using hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_2_13I2_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_2_13I2_sound_oai
