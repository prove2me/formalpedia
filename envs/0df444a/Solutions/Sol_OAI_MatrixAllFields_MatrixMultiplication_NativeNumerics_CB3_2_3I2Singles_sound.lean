-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I2Singles_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T14:27:19.004673+00:00
-- url     : https://prove2.me/submissions/64810a77-f867-4d02-a482-7226a16bfc89

import Mathlib
import Definitions.Def_OAIQ254M010
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkLog_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
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

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SupportedContraction
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
lemma B3_2_3Binary_eq (u : Shape) (hu : u ∈ shapes 4) :
    binaryParameter (shape 3 2 3) u = B3_2_3Binary u := by
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

lemma B3_2_3Little_sound (u : Shape) (w : Fin 3) (i : Fin 6) :
    (B3_2_3Little u w i).Encloses (littleLaw (shape 3 2 3) u w i : ℝ) := by
  by_cases hu : u ∈ shapes 4
  · simp only [B3_2_3Little, hu, ite_true, if_true]
    apply exact_rat_enclosed
    simp only [B3_2_3LittleRat, littleLaw, B3_2_3Binary_eq u hu]
  · simp only [B3_2_3Little, hu, ite_false, if_false]
    exact Ball.exact_sound _

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB3_2_3I2
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
lemma CB3_2_3I2S0_1_3E_4Log_sound : CB3_2_3I2S0_1_3E_4Log.Encloses (Real.log (CB3_2_3I2S0_1_3Value (4 : Fin 6))) := by
  exact log_exact_one_ball ((B3_2_3Little_sound (shape 0 1 3) ((stageBPriority (shape 3 2 3)) 2)) (4 : Fin 6))
lemma CB3_2_3I2S0_1_3E_4_sound : CB3_2_3I2S0_1_3E_4.Encloses (Foundation.entropyTerm (CB3_2_3I2S0_1_3Value (4 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B3_2_3Little_sound (shape 0 1 3) ((stageBPriority (shape 3 2 3)) 2)) (4 : Fin 6)) CB3_2_3I2S0_1_3E_4Log_sound) (by decide +kernel)
lemma CB3_2_3I2S0_1_3Terms_sound (a : Fin 6) :
    (CB3_2_3I2S0_1_3Terms a).Encloses (Foundation.entropyTerm (CB3_2_3I2S0_1_3Value a)) := by
  fin_cases a
  · exact (entropyTerm_zero_ball ((B3_2_3Little_sound (shape 0 1 3) ((stageBPriority (shape 3 2 3)) 2)) (0 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B3_2_3Little_sound (shape 0 1 3) ((stageBPriority (shape 3 2 3)) 2)) (1 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B3_2_3Little_sound (shape 0 1 3) ((stageBPriority (shape 3 2 3)) 2)) (2 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B3_2_3Little_sound (shape 0 1 3) ((stageBPriority (shape 3 2 3)) 2)) (3 : Fin 6)))
  · exact CB3_2_3I2S0_1_3E_4_sound
  · exact (entropyTerm_zero_ball ((B3_2_3Little_sound (shape 0 1 3) ((stageBPriority (shape 3 2 3)) 2)) (5 : Fin 6)))
lemma CB3_2_3I2S0_1_3Entropy_sound : CB3_2_3I2S0_1_3Entropy.Encloses (Foundation.finiteEntropy CB3_2_3I2S0_1_3Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_2_3I2S0_1_3Value CB3_2_3I2S0_1_3Terms CB3_2_3I2S0_1_3Terms_sound) (by decide +kernel)
lemma CB3_2_3I2S0_1_3Mass_sound : CB3_2_3I2S0_1_3Mass.Encloses (∑ a, CB3_2_3I2S0_1_3Value a) := by
  exact contains_sound (finSumBall_sound 6 (B3_2_3Little (shape 0 1 3) ((stageBPriority (shape 3 2 3)) 2)) CB3_2_3I2S0_1_3Value (B3_2_3Little_sound (shape 0 1 3) ((stageBPriority (shape 3 2 3)) 2))) (by decide +kernel)
lemma CB3_2_3I2S0_1_3MassTermLog_sound : CB3_2_3I2S0_1_3MassTermLog.Encloses (Real.log ((∑ a, CB3_2_3I2S0_1_3Value a))) := by
  exact log_exact_one_ball (CB3_2_3I2S0_1_3Mass_sound)
lemma CB3_2_3I2S0_1_3MassTerm_sound : CB3_2_3I2S0_1_3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_2_3I2S0_1_3Value a))) := by
  exact contains_sound (entropyTerm_ball (CB3_2_3I2S0_1_3Mass_sound) CB3_2_3I2S0_1_3MassTermLog_sound) (by decide +kernel)
lemma CB3_2_3I2S0_1_3H_sound : CB3_2_3I2S0_1_3H.Encloses (homogeneousEntropy CB3_2_3I2S0_1_3Value) := by
  exact contains_sound (homogeneous_enclosed CB3_2_3I2S0_1_3Value CB3_2_3I2S0_1_3MassTerm_sound CB3_2_3I2S0_1_3Entropy_sound) (by decide +kernel)
lemma CB3_2_3I2S0_2_2E_2Log_sound : CB3_2_3I2S0_2_2E_2Log.Encloses (Real.log (CB3_2_3I2S0_2_2Value (2 : Fin 6))) := by
  exact checkLog_sound logTwoBall_sound ((B3_2_3Little_sound (shape 0 2 2) ((stageBPriority (shape 3 2 3)) 2)) (2 : Fin 6)) (w := CB3_2_3I2S0_2_2E_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CB3_2_3I2S0_2_2E_2_sound : CB3_2_3I2S0_2_2E_2.Encloses (Foundation.entropyTerm (CB3_2_3I2S0_2_2Value (2 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B3_2_3Little_sound (shape 0 2 2) ((stageBPriority (shape 3 2 3)) 2)) (2 : Fin 6)) CB3_2_3I2S0_2_2E_2Log_sound) (by decide +kernel)
lemma CB3_2_3I2S0_2_2E_3Log_sound : CB3_2_3I2S0_2_2E_3Log.Encloses (Real.log (CB3_2_3I2S0_2_2Value (3 : Fin 6))) := by
  exact checkLog_sound logTwoBall_sound ((B3_2_3Little_sound (shape 0 2 2) ((stageBPriority (shape 3 2 3)) 2)) (3 : Fin 6)) (w := CB3_2_3I2S0_2_2E_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CB3_2_3I2S0_2_2E_3_sound : CB3_2_3I2S0_2_2E_3.Encloses (Foundation.entropyTerm (CB3_2_3I2S0_2_2Value (3 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B3_2_3Little_sound (shape 0 2 2) ((stageBPriority (shape 3 2 3)) 2)) (3 : Fin 6)) CB3_2_3I2S0_2_2E_3Log_sound) (by decide +kernel)
lemma CB3_2_3I2S0_2_2Terms_sound (a : Fin 6) :
    (CB3_2_3I2S0_2_2Terms a).Encloses (Foundation.entropyTerm (CB3_2_3I2S0_2_2Value a)) := by
  fin_cases a
  · exact (entropyTerm_zero_ball ((B3_2_3Little_sound (shape 0 2 2) ((stageBPriority (shape 3 2 3)) 2)) (0 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B3_2_3Little_sound (shape 0 2 2) ((stageBPriority (shape 3 2 3)) 2)) (1 : Fin 6)))
  · exact CB3_2_3I2S0_2_2E_2_sound
  · exact CB3_2_3I2S0_2_2E_3_sound
  · exact (entropyTerm_zero_ball ((B3_2_3Little_sound (shape 0 2 2) ((stageBPriority (shape 3 2 3)) 2)) (4 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B3_2_3Little_sound (shape 0 2 2) ((stageBPriority (shape 3 2 3)) 2)) (5 : Fin 6)))
lemma CB3_2_3I2S0_2_2Entropy_sound : CB3_2_3I2S0_2_2Entropy.Encloses (Foundation.finiteEntropy CB3_2_3I2S0_2_2Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_2_3I2S0_2_2Value CB3_2_3I2S0_2_2Terms CB3_2_3I2S0_2_2Terms_sound) (by decide +kernel)
lemma CB3_2_3I2S0_2_2Mass_sound : CB3_2_3I2S0_2_2Mass.Encloses (∑ a, CB3_2_3I2S0_2_2Value a) := by
  exact contains_sound (finSumBall_sound 6 (B3_2_3Little (shape 0 2 2) ((stageBPriority (shape 3 2 3)) 2)) CB3_2_3I2S0_2_2Value (B3_2_3Little_sound (shape 0 2 2) ((stageBPriority (shape 3 2 3)) 2))) (by decide +kernel)
lemma CB3_2_3I2S0_2_2MassTermLog_sound : CB3_2_3I2S0_2_2MassTermLog.Encloses (Real.log ((∑ a, CB3_2_3I2S0_2_2Value a))) := by
  exact log_exact_one_ball (CB3_2_3I2S0_2_2Mass_sound)
lemma CB3_2_3I2S0_2_2MassTerm_sound : CB3_2_3I2S0_2_2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_2_3I2S0_2_2Value a))) := by
  exact contains_sound (entropyTerm_ball (CB3_2_3I2S0_2_2Mass_sound) CB3_2_3I2S0_2_2MassTermLog_sound) (by decide +kernel)
lemma CB3_2_3I2S0_2_2H_sound : CB3_2_3I2S0_2_2H.Encloses (homogeneousEntropy CB3_2_3I2S0_2_2Value) := by
  exact contains_sound (homogeneous_enclosed CB3_2_3I2S0_2_2Value CB3_2_3I2S0_2_2MassTerm_sound CB3_2_3I2S0_2_2Entropy_sound) (by decide +kernel)
lemma CB3_2_3I2S1_0_3E_4Log_sound : CB3_2_3I2S1_0_3E_4Log.Encloses (Real.log (CB3_2_3I2S1_0_3Value (4 : Fin 6))) := by
  exact log_exact_one_ball ((B3_2_3Little_sound (shape 1 0 3) ((stageBPriority (shape 3 2 3)) 2)) (4 : Fin 6))
lemma CB3_2_3I2S1_0_3E_4_sound : CB3_2_3I2S1_0_3E_4.Encloses (Foundation.entropyTerm (CB3_2_3I2S1_0_3Value (4 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B3_2_3Little_sound (shape 1 0 3) ((stageBPriority (shape 3 2 3)) 2)) (4 : Fin 6)) CB3_2_3I2S1_0_3E_4Log_sound) (by decide +kernel)
lemma CB3_2_3I2S1_0_3Terms_sound (a : Fin 6) :
    (CB3_2_3I2S1_0_3Terms a).Encloses (Foundation.entropyTerm (CB3_2_3I2S1_0_3Value a)) := by
  fin_cases a
  · exact (entropyTerm_zero_ball ((B3_2_3Little_sound (shape 1 0 3) ((stageBPriority (shape 3 2 3)) 2)) (0 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B3_2_3Little_sound (shape 1 0 3) ((stageBPriority (shape 3 2 3)) 2)) (1 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B3_2_3Little_sound (shape 1 0 3) ((stageBPriority (shape 3 2 3)) 2)) (2 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B3_2_3Little_sound (shape 1 0 3) ((stageBPriority (shape 3 2 3)) 2)) (3 : Fin 6)))
  · exact CB3_2_3I2S1_0_3E_4_sound
  · exact (entropyTerm_zero_ball ((B3_2_3Little_sound (shape 1 0 3) ((stageBPriority (shape 3 2 3)) 2)) (5 : Fin 6)))
lemma CB3_2_3I2S1_0_3Entropy_sound : CB3_2_3I2S1_0_3Entropy.Encloses (Foundation.finiteEntropy CB3_2_3I2S1_0_3Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_2_3I2S1_0_3Value CB3_2_3I2S1_0_3Terms CB3_2_3I2S1_0_3Terms_sound) (by decide +kernel)
lemma CB3_2_3I2S1_0_3Mass_sound : CB3_2_3I2S1_0_3Mass.Encloses (∑ a, CB3_2_3I2S1_0_3Value a) := by
  exact contains_sound (finSumBall_sound 6 (B3_2_3Little (shape 1 0 3) ((stageBPriority (shape 3 2 3)) 2)) CB3_2_3I2S1_0_3Value (B3_2_3Little_sound (shape 1 0 3) ((stageBPriority (shape 3 2 3)) 2))) (by decide +kernel)
lemma CB3_2_3I2S1_0_3MassTermLog_sound : CB3_2_3I2S1_0_3MassTermLog.Encloses (Real.log ((∑ a, CB3_2_3I2S1_0_3Value a))) := by
  exact log_exact_one_ball (CB3_2_3I2S1_0_3Mass_sound)
lemma CB3_2_3I2S1_0_3MassTerm_sound : CB3_2_3I2S1_0_3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_2_3I2S1_0_3Value a))) := by
  exact contains_sound (entropyTerm_ball (CB3_2_3I2S1_0_3Mass_sound) CB3_2_3I2S1_0_3MassTermLog_sound) (by decide +kernel)
lemma CB3_2_3I2S1_0_3H_sound : CB3_2_3I2S1_0_3H.Encloses (homogeneousEntropy CB3_2_3I2S1_0_3Value) := by
  exact contains_sound (homogeneous_enclosed CB3_2_3I2S1_0_3Value CB3_2_3I2S1_0_3MassTerm_sound CB3_2_3I2S1_0_3Entropy_sound) (by decide +kernel)
lemma CB3_2_3I2S2_0_2E_2Log_sound : CB3_2_3I2S2_0_2E_2Log.Encloses (Real.log (CB3_2_3I2S2_0_2Value (2 : Fin 6))) := by
  exact checkLog_sound logTwoBall_sound ((B3_2_3Little_sound (shape 2 0 2) ((stageBPriority (shape 3 2 3)) 2)) (2 : Fin 6)) (w := CB3_2_3I2S2_0_2E_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CB3_2_3I2S2_0_2E_2_sound : CB3_2_3I2S2_0_2E_2.Encloses (Foundation.entropyTerm (CB3_2_3I2S2_0_2Value (2 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B3_2_3Little_sound (shape 2 0 2) ((stageBPriority (shape 3 2 3)) 2)) (2 : Fin 6)) CB3_2_3I2S2_0_2E_2Log_sound) (by decide +kernel)
lemma CB3_2_3I2S2_0_2E_3Log_sound : CB3_2_3I2S2_0_2E_3Log.Encloses (Real.log (CB3_2_3I2S2_0_2Value (3 : Fin 6))) := by
  exact checkLog_sound logTwoBall_sound ((B3_2_3Little_sound (shape 2 0 2) ((stageBPriority (shape 3 2 3)) 2)) (3 : Fin 6)) (w := CB3_2_3I2S2_0_2E_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CB3_2_3I2S2_0_2E_3_sound : CB3_2_3I2S2_0_2E_3.Encloses (Foundation.entropyTerm (CB3_2_3I2S2_0_2Value (3 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B3_2_3Little_sound (shape 2 0 2) ((stageBPriority (shape 3 2 3)) 2)) (3 : Fin 6)) CB3_2_3I2S2_0_2E_3Log_sound) (by decide +kernel)
lemma CB3_2_3I2S2_0_2Terms_sound (a : Fin 6) :
    (CB3_2_3I2S2_0_2Terms a).Encloses (Foundation.entropyTerm (CB3_2_3I2S2_0_2Value a)) := by
  fin_cases a
  · exact (entropyTerm_zero_ball ((B3_2_3Little_sound (shape 2 0 2) ((stageBPriority (shape 3 2 3)) 2)) (0 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B3_2_3Little_sound (shape 2 0 2) ((stageBPriority (shape 3 2 3)) 2)) (1 : Fin 6)))
  · exact CB3_2_3I2S2_0_2E_2_sound
  · exact CB3_2_3I2S2_0_2E_3_sound
  · exact (entropyTerm_zero_ball ((B3_2_3Little_sound (shape 2 0 2) ((stageBPriority (shape 3 2 3)) 2)) (4 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B3_2_3Little_sound (shape 2 0 2) ((stageBPriority (shape 3 2 3)) 2)) (5 : Fin 6)))
lemma CB3_2_3I2S2_0_2Entropy_sound : CB3_2_3I2S2_0_2Entropy.Encloses (Foundation.finiteEntropy CB3_2_3I2S2_0_2Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_2_3I2S2_0_2Value CB3_2_3I2S2_0_2Terms CB3_2_3I2S2_0_2Terms_sound) (by decide +kernel)
lemma CB3_2_3I2S2_0_2Mass_sound : CB3_2_3I2S2_0_2Mass.Encloses (∑ a, CB3_2_3I2S2_0_2Value a) := by
  exact contains_sound (finSumBall_sound 6 (B3_2_3Little (shape 2 0 2) ((stageBPriority (shape 3 2 3)) 2)) CB3_2_3I2S2_0_2Value (B3_2_3Little_sound (shape 2 0 2) ((stageBPriority (shape 3 2 3)) 2))) (by decide +kernel)
lemma CB3_2_3I2S2_0_2MassTermLog_sound : CB3_2_3I2S2_0_2MassTermLog.Encloses (Real.log ((∑ a, CB3_2_3I2S2_0_2Value a))) := by
  exact log_exact_one_ball (CB3_2_3I2S2_0_2Mass_sound)
lemma CB3_2_3I2S2_0_2MassTerm_sound : CB3_2_3I2S2_0_2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_2_3I2S2_0_2Value a))) := by
  exact contains_sound (entropyTerm_ball (CB3_2_3I2S2_0_2Mass_sound) CB3_2_3I2S2_0_2MassTermLog_sound) (by decide +kernel)
lemma CB3_2_3I2S2_0_2H_sound : CB3_2_3I2S2_0_2H.Encloses (homogeneousEntropy CB3_2_3I2S2_0_2Value) := by
  exact contains_sound (homogeneous_enclosed CB3_2_3I2S2_0_2Value CB3_2_3I2S2_0_2MassTerm_sound CB3_2_3I2S2_0_2Entropy_sound) (by decide +kernel)
lemma CB3_2_3I2S3_0_1E_1Log_sound : CB3_2_3I2S3_0_1E_1Log.Encloses (Real.log (CB3_2_3I2S3_0_1Value (1 : Fin 6))) := by
  exact log_exact_one_ball ((B3_2_3Little_sound (shape 3 0 1) ((stageBPriority (shape 3 2 3)) 2)) (1 : Fin 6))
lemma CB3_2_3I2S3_0_1E_1_sound : CB3_2_3I2S3_0_1E_1.Encloses (Foundation.entropyTerm (CB3_2_3I2S3_0_1Value (1 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B3_2_3Little_sound (shape 3 0 1) ((stageBPriority (shape 3 2 3)) 2)) (1 : Fin 6)) CB3_2_3I2S3_0_1E_1Log_sound) (by decide +kernel)
lemma CB3_2_3I2S3_0_1Terms_sound (a : Fin 6) :
    (CB3_2_3I2S3_0_1Terms a).Encloses (Foundation.entropyTerm (CB3_2_3I2S3_0_1Value a)) := by
  fin_cases a
  · exact (entropyTerm_zero_ball ((B3_2_3Little_sound (shape 3 0 1) ((stageBPriority (shape 3 2 3)) 2)) (0 : Fin 6)))
  · exact CB3_2_3I2S3_0_1E_1_sound
  · exact (entropyTerm_zero_ball ((B3_2_3Little_sound (shape 3 0 1) ((stageBPriority (shape 3 2 3)) 2)) (2 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B3_2_3Little_sound (shape 3 0 1) ((stageBPriority (shape 3 2 3)) 2)) (3 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B3_2_3Little_sound (shape 3 0 1) ((stageBPriority (shape 3 2 3)) 2)) (4 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B3_2_3Little_sound (shape 3 0 1) ((stageBPriority (shape 3 2 3)) 2)) (5 : Fin 6)))
lemma CB3_2_3I2S3_0_1Entropy_sound : CB3_2_3I2S3_0_1Entropy.Encloses (Foundation.finiteEntropy CB3_2_3I2S3_0_1Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_2_3I2S3_0_1Value CB3_2_3I2S3_0_1Terms CB3_2_3I2S3_0_1Terms_sound) (by decide +kernel)
lemma CB3_2_3I2S3_0_1Mass_sound : CB3_2_3I2S3_0_1Mass.Encloses (∑ a, CB3_2_3I2S3_0_1Value a) := by
  exact contains_sound (finSumBall_sound 6 (B3_2_3Little (shape 3 0 1) ((stageBPriority (shape 3 2 3)) 2)) CB3_2_3I2S3_0_1Value (B3_2_3Little_sound (shape 3 0 1) ((stageBPriority (shape 3 2 3)) 2))) (by decide +kernel)
lemma CB3_2_3I2S3_0_1MassTermLog_sound : CB3_2_3I2S3_0_1MassTermLog.Encloses (Real.log ((∑ a, CB3_2_3I2S3_0_1Value a))) := by
  exact log_exact_one_ball (CB3_2_3I2S3_0_1Mass_sound)
lemma CB3_2_3I2S3_0_1MassTerm_sound : CB3_2_3I2S3_0_1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_2_3I2S3_0_1Value a))) := by
  exact contains_sound (entropyTerm_ball (CB3_2_3I2S3_0_1Mass_sound) CB3_2_3I2S3_0_1MassTermLog_sound) (by decide +kernel)
lemma CB3_2_3I2S3_0_1H_sound : CB3_2_3I2S3_0_1H.Encloses (homogeneousEntropy CB3_2_3I2S3_0_1Value) := by
  exact contains_sound (homogeneous_enclosed CB3_2_3I2S3_0_1Value CB3_2_3I2S3_0_1MassTerm_sound CB3_2_3I2S3_0_1Entropy_sound) (by decide +kernel)
lemma CB3_2_3I2Singles_sound_oai (u : Shape) (hu : u ∈ below (shape 3 2 3))
    (hd : designated (stageBPriority (shape 3 2 3)) 2 u) :
    (CB3_2_3I2Singles u).Encloses (homogeneousEntropy ((fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 2) a : ℝ)) u)) := by
  rw [B3_2_3_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact CB3_2_3I2S0_1_3H_sound
  · exact CB3_2_3I2S0_2_2H_sound
  · exact CB3_2_3I2S1_0_3H_sound
  · exact (show ¬ designated (stageBPriority (shape 3 2 3)) 2 (shape 1 1 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (stageBPriority (shape 3 2 3)) 2 (shape 1 2 1) by decide +kernel) hd |>.elim
  · exact CB3_2_3I2S2_0_2H_sound
  · exact (show ¬ designated (stageBPriority (shape 3 2 3)) 2 (shape 2 1 1) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (stageBPriority (shape 3 2 3)) 2 (shape 2 2 0) by decide +kernel) hd |>.elim
  · exact CB3_2_3I2S3_0_1H_sound
  · exact (show ¬ designated (stageBPriority (shape 3 2 3)) 2 (shape 3 1 0) by decide +kernel) hd |>.elim

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I2Singles_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I2Singles_sound_oai
