-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I0_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T07:28:58.113698+00:00
-- url     : https://prove2.me/submissions/aa37c3be-4183-4027-8f9d-6ed8962cbd0f

import Mathlib
import Definitions.Def_OAIQ254M010
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_mul_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkLog_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_CompactCertificate_entropyLookup_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B3_2_3Den_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B3_2_3Raw_sound
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
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitB5_1_2
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

lemma B3_2_3_below : below (shape 3 2 3) = [
  (shape 0 1 3),
  (shape 0 2 2),
  (shape 1 0 3),
  (shape 1 1 2),
  (shape 1 2 1),
  (shape 2 0 2),
  (shape 2 1 1),
  (shape 2 2 0),
  (shape 3 0 1),
  (shape 3 1 0)] := by decide +kernel
lemma B3_2_3Den_positive : 0 < B3_2_3Den.lower := by decide +kernel
lemma B3_2_3Law_check_0_1_3 : contains (.mul (B3_2_3Raw (shape 0 1 3)) (.inv B3_2_3Den)) (B3_2_3Table (shape 0 1 3)) = true := by decide +kernel
lemma B3_2_3Law_check_0_2_2 : contains (.mul (B3_2_3Raw (shape 0 2 2)) (.inv B3_2_3Den)) (B3_2_3Table (shape 0 2 2)) = true := by decide +kernel
lemma B3_2_3Law_check_1_0_3 : contains (.mul (B3_2_3Raw (shape 1 0 3)) (.inv B3_2_3Den)) (B3_2_3Table (shape 1 0 3)) = true := by decide +kernel
lemma B3_2_3Law_check_1_1_2 : contains (.mul (B3_2_3Raw (shape 1 1 2)) (.inv B3_2_3Den)) (B3_2_3Table (shape 1 1 2)) = true := by decide +kernel
lemma B3_2_3Law_check_1_2_1 : contains (.mul (B3_2_3Raw (shape 1 2 1)) (.inv B3_2_3Den)) (B3_2_3Table (shape 1 2 1)) = true := by decide +kernel
lemma B3_2_3Law_check_2_0_2 : contains (.mul (B3_2_3Raw (shape 2 0 2)) (.inv B3_2_3Den)) (B3_2_3Table (shape 2 0 2)) = true := by decide +kernel
lemma B3_2_3Law_check_2_1_1 : contains (.mul (B3_2_3Raw (shape 2 1 1)) (.inv B3_2_3Den)) (B3_2_3Table (shape 2 1 1)) = true := by decide +kernel
lemma B3_2_3Law_check_2_2_0 : contains (.mul (B3_2_3Raw (shape 2 2 0)) (.inv B3_2_3Den)) (B3_2_3Table (shape 2 2 0)) = true := by decide +kernel
lemma B3_2_3Law_check_3_0_1 : contains (.mul (B3_2_3Raw (shape 3 0 1)) (.inv B3_2_3Den)) (B3_2_3Table (shape 3 0 1)) = true := by decide +kernel
lemma B3_2_3Law_check_3_1_0 : contains (.mul (B3_2_3Raw (shape 3 1 0)) (.inv B3_2_3Den)) (B3_2_3Table (shape 3 1 0)) = true := by decide +kernel
lemma B3_2_3Law_check (u : Shape) (hu : u ∈ below (shape 3 2 3)) :
    contains (.mul (B3_2_3Raw u) (.inv B3_2_3Den)) (B3_2_3Table u) = true := by
  rw [B3_2_3_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B3_2_3Law_check_0_1_3
  · exact B3_2_3Law_check_0_2_2
  · exact B3_2_3Law_check_1_0_3
  · exact B3_2_3Law_check_1_1_2
  · exact B3_2_3Law_check_1_2_1
  · exact B3_2_3Law_check_2_0_2
  · exact B3_2_3Law_check_2_1_1
  · exact B3_2_3Law_check_2_2_0
  · exact B3_2_3Law_check_3_0_1
  · exact B3_2_3Law_check_3_1_0
lemma B3_2_3Law_sound (u : Shape) :
    (B3_2_3Law u).Encloses (stageBLaw (shape 3 2 3) u : ℝ) := by
  by_cases hu : u ∈ below (shape 3 2 3)
  · have h := contains_sound (Ball.mul_sound (B3_2_3Raw_sound u hu)
      (Ball.inv_sound B3_2_3Den_sound B3_2_3Den_positive)) (B3_2_3Law_check u hu)
    simpa only [B3_2_3Law, hu, ite_true, if_true, stageBLaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [B3_2_3Law, hu, ite_false, if_false, stageBLaw, splitLaw, Rat.cast_zero]
    simpa only [Rat.cast_zero] using Ball.exact_sound 0

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB3_2_3I0
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
lemma CB3_2_3I0Raw_sound (a : Fin 17) :
    (CB3_2_3I0Raw a).Encloses (CB3_2_3I0Value a) := by
  exact marginalBall_sound (below (shape 3 2 3)) B3_2_3Law (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (fun u _ => B3_2_3Law_sound u) ((stageBPriority (shape 3 2 3)) 0) a
lemma CB3_2_3I0Certificates_valid :
    CB3_2_3I0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB3_2_3I0P_check : ∀ a : Fin 17, contains (CB3_2_3I0Raw a) (CB3_2_3I0P a) = true := by
  decide +kernel
lemma CB3_2_3I0P_sound (a : Fin 17) :
    (CB3_2_3I0P a).Encloses (CB3_2_3I0Value a) :=
  contains_sound (CB3_2_3I0Raw_sound a) (CB3_2_3I0P_check a)
lemma CB3_2_3I0Terms_sound (a : Fin 17) :
    (CB3_2_3I0Terms a).Encloses (Foundation.entropyTerm (CB3_2_3I0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_2_3I0Certificates_valid
    (CB3_2_3I0CertificateIndex a) (CB3_2_3I0P_sound a)
lemma CB3_2_3I0Entropy_sound : CB3_2_3I0Entropy.Encloses (Foundation.finiteEntropy CB3_2_3I0Value) := by
  exact contains_sound (entropyFin_enclosed 17 CB3_2_3I0Value CB3_2_3I0Terms CB3_2_3I0Terms_sound) (by decide +kernel)
lemma CB3_2_3I0Mass_sound : CB3_2_3I0Mass.Encloses (∑ a, CB3_2_3I0Value a) := by
  exact contains_sound (finSumBall_sound 17 CB3_2_3I0P CB3_2_3I0Value CB3_2_3I0P_sound) (by decide +kernel)
lemma CB3_2_3I0MassTermLog_sound : CB3_2_3I0MassTermLog.Encloses (Real.log ((∑ a, CB3_2_3I0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB3_2_3I0Mass_sound) (w := CB3_2_3I0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CB3_2_3I0MassTerm_sound : CB3_2_3I0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_2_3I0Value a))) := by
  exact contains_sound (entropyTerm_ball (CB3_2_3I0Mass_sound) CB3_2_3I0MassTermLog_sound) (by decide +kernel)
lemma CB3_2_3I0H_sound : CB3_2_3I0H.Encloses (homogeneousEntropy CB3_2_3I0Value) := by
  exact contains_sound (homogeneous_enclosed CB3_2_3I0Value CB3_2_3I0MassTerm_sound CB3_2_3I0Entropy_sound) (by decide +kernel)
lemma CB3_2_3I0_sound_oai : CB3_2_3I0H.Encloses (stageBCapacity (shape 3 2 3) 0) := by
  exact CB3_2_3I0H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I0_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I0_sound_oai
