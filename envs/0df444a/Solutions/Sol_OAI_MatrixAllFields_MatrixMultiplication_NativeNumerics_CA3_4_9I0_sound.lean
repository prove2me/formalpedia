-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_4_9I0_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T07:19:32.543643+00:00
-- url     : https://prove2.me/submissions/90ab836b-d4bf-4f9a-93ff-a58352c343af

import Mathlib
import Definitions.Def_OAIQ254M009
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_mul_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkLog_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_CompactCertificate_entropyLookup_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_A3_4_9Den_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_A3_4_9Raw_sound
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
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators

lemma entropyFin_enclosed (n : ℕ) (p : Fin n → ℝ) (bs : Fin n → Ball)
    (h : ∀ i, (bs i).Encloses (Foundation.entropyTerm (p i))) :
    (finSumBall n bs).Encloses (Foundation.finiteEntropy p) :=
  finSumBall_sound n _ _ h

lemma homogeneous_enclosed {A : Type*} [Fintype A] (p : A → ℝ)
    {b e : Ball} (hb : b.Encloses (Foundation.entropyTerm (∑ a, p a)))
    (he : e.Encloses (Foundation.finiteEntropy p)) :
    (Ball.add (Ball.neg b) e).Encloses (homogeneousEntropy p) := by
  convert Ball.add_sound (Ball.neg_sound hb) he using 1
  all_goals try with_reducible_and_instances rfl
  simp only [homogeneousEntropy, Foundation.entropyTerm, neg_mul, neg_neg]

lemma marginalBall_sound (support : List Shape) (bs : Shape → Ball) (p : Shape → ℝ)
    (h : ∀ u ∈ support, (bs u).Encloses (p u)) (side : Fin 3) (k : Fin 17) :
    (marginalBall support bs side k).Encloses (marginal support p side k) := by
  apply listSumBall_sound
  intro u hu
  by_cases hk : u side = k.val
  · simpa only [hk, ite_true, if_true] using h u hu
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
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA3_4_9I0
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
lemma CA3_4_9I0Raw_sound (a : Fin 17) :
    (CA3_4_9I0Raw a).Encloses (CA3_4_9I0Value a) := by
  exact marginalBall_sound (below (shape 3 4 9)) A3_4_9Law (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (fun u _ => A3_4_9Law_sound u) ((Equiv.refl (Fin 3)) 0) a
lemma CA3_4_9I0Certificates_valid :
    CA3_4_9I0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA3_4_9I0P_check : ∀ a : Fin 17, contains (CA3_4_9I0Raw a) (CA3_4_9I0P a) = true := by
  decide +kernel
lemma CA3_4_9I0P_sound (a : Fin 17) :
    (CA3_4_9I0P a).Encloses (CA3_4_9I0Value a) :=
  contains_sound (CA3_4_9I0Raw_sound a) (CA3_4_9I0P_check a)
lemma CA3_4_9I0Terms_sound (a : Fin 17) :
    (CA3_4_9I0Terms a).Encloses (Foundation.entropyTerm (CA3_4_9I0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_4_9I0Certificates_valid
    (CA3_4_9I0CertificateIndex a) (CA3_4_9I0P_sound a)
lemma CA3_4_9I0Entropy_sound : CA3_4_9I0Entropy.Encloses (Foundation.finiteEntropy CA3_4_9I0Value) := by
  exact contains_sound (entropyFin_enclosed 17 CA3_4_9I0Value CA3_4_9I0Terms CA3_4_9I0Terms_sound) (by decide +kernel)
lemma CA3_4_9I0Mass_sound : CA3_4_9I0Mass.Encloses (∑ a, CA3_4_9I0Value a) := by
  exact contains_sound (finSumBall_sound 17 CA3_4_9I0P CA3_4_9I0Value CA3_4_9I0P_sound) (by decide +kernel)
lemma CA3_4_9I0MassTermLog_sound : CA3_4_9I0MassTermLog.Encloses (Real.log ((∑ a, CA3_4_9I0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_4_9I0Mass_sound) (w := CA3_4_9I0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CA3_4_9I0MassTerm_sound : CA3_4_9I0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_4_9I0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_4_9I0Mass_sound) CA3_4_9I0MassTermLog_sound) (by decide +kernel)
lemma CA3_4_9I0H_sound : CA3_4_9I0H.Encloses (homogeneousEntropy CA3_4_9I0Value) := by
  exact contains_sound (homogeneous_enclosed CA3_4_9I0Value CA3_4_9I0MassTerm_sound CA3_4_9I0Entropy_sound) (by decide +kernel)
lemma CA3_4_9I0_sound_oai : CA3_4_9I0H.Encloses (stageACapacity (shape 3 4 9) 0) := by
  exact CA3_4_9I0H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_4_9I0_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_4_9I0_sound_oai
