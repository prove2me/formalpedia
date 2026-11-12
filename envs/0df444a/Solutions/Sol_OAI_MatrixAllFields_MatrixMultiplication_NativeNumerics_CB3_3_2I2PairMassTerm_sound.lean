-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I2PairMassTerm_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T14:29:06.247183+00:00
-- url     : https://prove2.me/submissions/a1c0b23c-fcf7-4de8-b8c8-e9ba60fc9386

import Mathlib
import Definitions.Def_OAIQ254M010
import Definitions.Def_OAIQ254M011
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_mul_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkLog_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B3_3_2Den_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B3_3_2Raw_sound
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
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal3_3_2
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
lemma B3_3_2_below : below (shape 3 3 2) = [
  (shape 0 2 2),
  (shape 0 3 1),
  (shape 1 1 2),
  (shape 1 2 1),
  (shape 1 3 0),
  (shape 2 0 2),
  (shape 2 1 1),
  (shape 2 2 0),
  (shape 3 0 1),
  (shape 3 1 0)] := by decide +kernel
lemma B3_3_2Den_positive : 0 < B3_3_2Den.lower := by decide +kernel
lemma B3_3_2Law_check_0_2_2 : contains (.mul (B3_3_2Raw (shape 0 2 2)) (.inv B3_3_2Den)) (B3_3_2Table (shape 0 2 2)) = true := by decide +kernel
lemma B3_3_2Law_check_0_3_1 : contains (.mul (B3_3_2Raw (shape 0 3 1)) (.inv B3_3_2Den)) (B3_3_2Table (shape 0 3 1)) = true := by decide +kernel
lemma B3_3_2Law_check_1_1_2 : contains (.mul (B3_3_2Raw (shape 1 1 2)) (.inv B3_3_2Den)) (B3_3_2Table (shape 1 1 2)) = true := by decide +kernel
lemma B3_3_2Law_check_1_2_1 : contains (.mul (B3_3_2Raw (shape 1 2 1)) (.inv B3_3_2Den)) (B3_3_2Table (shape 1 2 1)) = true := by decide +kernel
lemma B3_3_2Law_check_1_3_0 : contains (.mul (B3_3_2Raw (shape 1 3 0)) (.inv B3_3_2Den)) (B3_3_2Table (shape 1 3 0)) = true := by decide +kernel
lemma B3_3_2Law_check_2_0_2 : contains (.mul (B3_3_2Raw (shape 2 0 2)) (.inv B3_3_2Den)) (B3_3_2Table (shape 2 0 2)) = true := by decide +kernel
lemma B3_3_2Law_check_2_1_1 : contains (.mul (B3_3_2Raw (shape 2 1 1)) (.inv B3_3_2Den)) (B3_3_2Table (shape 2 1 1)) = true := by decide +kernel
lemma B3_3_2Law_check_2_2_0 : contains (.mul (B3_3_2Raw (shape 2 2 0)) (.inv B3_3_2Den)) (B3_3_2Table (shape 2 2 0)) = true := by decide +kernel
lemma B3_3_2Law_check_3_0_1 : contains (.mul (B3_3_2Raw (shape 3 0 1)) (.inv B3_3_2Den)) (B3_3_2Table (shape 3 0 1)) = true := by decide +kernel
lemma B3_3_2Law_check_3_1_0 : contains (.mul (B3_3_2Raw (shape 3 1 0)) (.inv B3_3_2Den)) (B3_3_2Table (shape 3 1 0)) = true := by decide +kernel
lemma B3_3_2Law_check (u : Shape) (hu : u ∈ below (shape 3 3 2)) :
    contains (.mul (B3_3_2Raw u) (.inv B3_3_2Den)) (B3_3_2Table u) = true := by
  rw [B3_3_2_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B3_3_2Law_check_0_2_2
  · exact B3_3_2Law_check_0_3_1
  · exact B3_3_2Law_check_1_1_2
  · exact B3_3_2Law_check_1_2_1
  · exact B3_3_2Law_check_1_3_0
  · exact B3_3_2Law_check_2_0_2
  · exact B3_3_2Law_check_2_1_1
  · exact B3_3_2Law_check_2_2_0
  · exact B3_3_2Law_check_3_0_1
  · exact B3_3_2Law_check_3_1_0
lemma B3_3_2Law_sound (u : Shape) :
    (B3_3_2Law u).Encloses (stageBLaw (shape 3 3 2) u : ℝ) := by
  by_cases hu : u ∈ below (shape 3 3 2)
  · have h := contains_sound (Ball.mul_sound (B3_3_2Raw_sound u hu)
      (Ball.inv_sound B3_3_2Den_sound B3_3_2Den_positive)) (B3_3_2Law_check u hu)
    simpa only [B3_3_2Law, hu, ite_true, if_true, stageBLaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [B3_3_2Law, hu, ite_false, if_false, stageBLaw, splitLaw, Rat.cast_zero]
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
lemma B3_3_2Binary_eq (u : Shape) (hu : u ∈ shapes 4) :
    binaryParameter (shape 3 3 2) u = B3_3_2Binary u := by
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

lemma B3_3_2Little_sound (u : Shape) (w : Fin 3) (i : Fin 6) :
    (B3_3_2Little u w i).Encloses (littleLaw (shape 3 3 2) u w i : ℝ) := by
  by_cases hu : u ∈ shapes 4
  · simp only [B3_3_2Little, hu, ite_true, if_true]
    apply exact_rat_enclosed
    simp only [B3_3_2LittleRat, littleLaw, B3_3_2Binary_eq u hu]
  · simp only [B3_3_2Little, hu, ite_false, if_false]
    exact Ball.exact_sound _

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB3_3_2I2
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
lemma CB3_3_2I2PairRaw_sound (a : PairSlot) :
    (CB3_3_2I2PairRaw a).Encloses (CB3_3_2I2PairValue a) := by
  exact pairLawBall_sound_on (below (shape 3 3 2)) (shape 3 3 2) B3_3_2Law (fun u => (stageBLaw (shape 3 3 2) u : ℝ)) (fun u => B3_3_2Little u ((stageBPriority (shape 3 3 2)) 2)) (fun u a => (littleLaw (shape 3 3 2) u ((stageBPriority (shape 3 3 2)) 2) a : ℝ)) (fun u _ => B3_3_2Law_sound u) (fun u _ a => B3_3_2Little_sound u ((stageBPriority (shape 3 3 2)) 2) a) (fun u _ a => B3_3_2Little_sound (complement (shape 3 3 2) u) ((stageBPriority (shape 3 3 2)) 2) a) a
lemma CB3_3_2I2PairP_check : ∀ a : PairSlot, contains (CB3_3_2I2PairRaw a) (CB3_3_2I2PairP a) = true := by
  decide +kernel
lemma CB3_3_2I2PairP_sound (a : PairSlot) :
    (CB3_3_2I2PairP a).Encloses (CB3_3_2I2PairValue a) :=
  contains_sound (CB3_3_2I2PairRaw_sound a) (CB3_3_2I2PairP_check a)
lemma CB3_3_2I2PairMass_sound : CB3_3_2I2PairMass.Encloses (∑ a, CB3_3_2I2PairValue a) := by
  exact contains_sound (pairSumBall_sound CB3_3_2I2PairP CB3_3_2I2PairValue CB3_3_2I2PairP_sound) (by decide +kernel)
lemma CB3_3_2I2PairMassTermLog_sound : CB3_3_2I2PairMassTermLog.Encloses (Real.log ((∑ a, CB3_3_2I2PairValue a))) := by
  exact checkLog_sound logTwoBall_sound (CB3_3_2I2PairMass_sound) (w := CB3_3_2I2PairMassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CB3_3_2I2PairMassTerm_sound_oai : CB3_3_2I2PairMassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_3_2I2PairValue a))) := by
  exact contains_sound (entropyTerm_ball (CB3_3_2I2PairMass_sound) CB3_3_2I2PairMassTermLog_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I2PairMassTerm_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I2PairMassTerm_sound_oai
