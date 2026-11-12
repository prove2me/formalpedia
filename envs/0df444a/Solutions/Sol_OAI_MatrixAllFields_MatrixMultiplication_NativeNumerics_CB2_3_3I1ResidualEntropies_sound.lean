-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB2_3_3I1ResidualEntropies_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T13:18:57.617105+00:00
-- url     : https://prove2.me/submissions/872ae057-d451-4a06-b0d5-156a4983d5b6

import Mathlib
import Definitions.Def_OAIQ254M010
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkLog_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_CompactCertificate_entropyLookup_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_3_3I1R0MassTerm_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_3_3I1R0Terms_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_3_3I1R10P_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_3_3I1R11Raw_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_3_3I1R12Raw_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_3_3I1R13Raw_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_3_3I1R14Raw_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_3_3I1R15Raw_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_3_3I1R16Raw_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_3_3I1R1Raw_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_3_3I1R2H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_3_3I1R3H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_3_3I1R4Raw_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_3_3I1R5Raw_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_3_3I1R6Raw_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_3_3I1R7Raw_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_3_3I1R8Raw_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_3_3I1R9Raw_sound
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
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB2_3_3I1
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
lemma CB2_3_3I1R0Entropy_sound : CB2_3_3I1R0Entropy.Encloses (Foundation.finiteEntropy CB2_3_3I1R0Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_3_3I1R0Value CB2_3_3I1R0Terms CB2_3_3I1R0Terms_sound) (by decide +kernel)
lemma CB2_3_3I1R0H_sound : CB2_3_3I1R0H.Encloses (homogeneousEntropy CB2_3_3I1R0Value) := by
  exact contains_sound (homogeneous_enclosed CB2_3_3I1R0Value CB2_3_3I1R0MassTerm_sound CB2_3_3I1R0Entropy_sound) (by decide +kernel)
lemma CB2_3_3I1R1Certificates_valid :
    CB2_3_3I1R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB2_3_3I1R1P_check : ∀ a : Fin 6, contains (CB2_3_3I1R1Raw a) (CB2_3_3I1R1P a) = true := by
  decide +kernel
lemma CB2_3_3I1R1P_sound (a : Fin 6) :
    (CB2_3_3I1R1P a).Encloses (CB2_3_3I1R1Value a) :=
  contains_sound (CB2_3_3I1R1Raw_sound a) (CB2_3_3I1R1P_check a)
lemma CB2_3_3I1R1Terms_sound (a : Fin 6) :
    (CB2_3_3I1R1Terms a).Encloses (Foundation.entropyTerm (CB2_3_3I1R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_3_3I1R1Certificates_valid
    (CB2_3_3I1R1CertificateIndex a) (CB2_3_3I1R1P_sound a)
lemma CB2_3_3I1R1Entropy_sound : CB2_3_3I1R1Entropy.Encloses (Foundation.finiteEntropy CB2_3_3I1R1Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_3_3I1R1Value CB2_3_3I1R1Terms CB2_3_3I1R1Terms_sound) (by decide +kernel)
lemma CB2_3_3I1R1Mass_sound : CB2_3_3I1R1Mass.Encloses (∑ a, CB2_3_3I1R1Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_3_3I1R1P CB2_3_3I1R1Value CB2_3_3I1R1P_sound) (by decide +kernel)
lemma CB2_3_3I1R1MassTermLog_sound : CB2_3_3I1R1MassTermLog.Encloses (Real.log ((∑ a, CB2_3_3I1R1Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB2_3_3I1R1Mass_sound) (w := CB2_3_3I1R1MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CB2_3_3I1R1MassTerm_sound : CB2_3_3I1R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_3_3I1R1Value a))) := by
  exact contains_sound (entropyTerm_ball (CB2_3_3I1R1Mass_sound) CB2_3_3I1R1MassTermLog_sound) (by decide +kernel)
lemma CB2_3_3I1R1H_sound : CB2_3_3I1R1H.Encloses (homogeneousEntropy CB2_3_3I1R1Value) := by
  exact contains_sound (homogeneous_enclosed CB2_3_3I1R1Value CB2_3_3I1R1MassTerm_sound CB2_3_3I1R1Entropy_sound) (by decide +kernel)
lemma CB2_3_3I1R4Certificates_valid :
    CB2_3_3I1R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB2_3_3I1R4P_check : ∀ a : Fin 6, contains (CB2_3_3I1R4Raw a) (CB2_3_3I1R4P a) = true := by
  decide +kernel
lemma CB2_3_3I1R4P_sound (a : Fin 6) :
    (CB2_3_3I1R4P a).Encloses (CB2_3_3I1R4Value a) :=
  contains_sound (CB2_3_3I1R4Raw_sound a) (CB2_3_3I1R4P_check a)
lemma CB2_3_3I1R4Terms_sound (a : Fin 6) :
    (CB2_3_3I1R4Terms a).Encloses (Foundation.entropyTerm (CB2_3_3I1R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_3_3I1R4Certificates_valid
    (CB2_3_3I1R4CertificateIndex a) (CB2_3_3I1R4P_sound a)
lemma CB2_3_3I1R4Entropy_sound : CB2_3_3I1R4Entropy.Encloses (Foundation.finiteEntropy CB2_3_3I1R4Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_3_3I1R4Value CB2_3_3I1R4Terms CB2_3_3I1R4Terms_sound) (by decide +kernel)
lemma CB2_3_3I1R4Mass_sound : CB2_3_3I1R4Mass.Encloses (∑ a, CB2_3_3I1R4Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_3_3I1R4P CB2_3_3I1R4Value CB2_3_3I1R4P_sound) (by decide +kernel)
lemma CB2_3_3I1R4MassTerm_sound : CB2_3_3I1R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_3_3I1R4Value a))) :=
  entropyTerm_zero_ball (CB2_3_3I1R4Mass_sound)
lemma CB2_3_3I1R4H_sound : CB2_3_3I1R4H.Encloses (homogeneousEntropy CB2_3_3I1R4Value) := by
  exact contains_sound (homogeneous_enclosed CB2_3_3I1R4Value CB2_3_3I1R4MassTerm_sound CB2_3_3I1R4Entropy_sound) (by decide +kernel)
lemma CB2_3_3I1R5Certificates_valid :
    CB2_3_3I1R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB2_3_3I1R5P_check : ∀ a : Fin 6, contains (CB2_3_3I1R5Raw a) (CB2_3_3I1R5P a) = true := by
  decide +kernel
lemma CB2_3_3I1R5P_sound (a : Fin 6) :
    (CB2_3_3I1R5P a).Encloses (CB2_3_3I1R5Value a) :=
  contains_sound (CB2_3_3I1R5Raw_sound a) (CB2_3_3I1R5P_check a)
lemma CB2_3_3I1R5Terms_sound (a : Fin 6) :
    (CB2_3_3I1R5Terms a).Encloses (Foundation.entropyTerm (CB2_3_3I1R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_3_3I1R5Certificates_valid
    (CB2_3_3I1R5CertificateIndex a) (CB2_3_3I1R5P_sound a)
lemma CB2_3_3I1R5Entropy_sound : CB2_3_3I1R5Entropy.Encloses (Foundation.finiteEntropy CB2_3_3I1R5Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_3_3I1R5Value CB2_3_3I1R5Terms CB2_3_3I1R5Terms_sound) (by decide +kernel)
lemma CB2_3_3I1R5Mass_sound : CB2_3_3I1R5Mass.Encloses (∑ a, CB2_3_3I1R5Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_3_3I1R5P CB2_3_3I1R5Value CB2_3_3I1R5P_sound) (by decide +kernel)
lemma CB2_3_3I1R5MassTerm_sound : CB2_3_3I1R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_3_3I1R5Value a))) :=
  entropyTerm_zero_ball (CB2_3_3I1R5Mass_sound)
lemma CB2_3_3I1R5H_sound : CB2_3_3I1R5H.Encloses (homogeneousEntropy CB2_3_3I1R5Value) := by
  exact contains_sound (homogeneous_enclosed CB2_3_3I1R5Value CB2_3_3I1R5MassTerm_sound CB2_3_3I1R5Entropy_sound) (by decide +kernel)
lemma CB2_3_3I1R6Certificates_valid :
    CB2_3_3I1R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB2_3_3I1R6P_check : ∀ a : Fin 6, contains (CB2_3_3I1R6Raw a) (CB2_3_3I1R6P a) = true := by
  decide +kernel
lemma CB2_3_3I1R6P_sound (a : Fin 6) :
    (CB2_3_3I1R6P a).Encloses (CB2_3_3I1R6Value a) :=
  contains_sound (CB2_3_3I1R6Raw_sound a) (CB2_3_3I1R6P_check a)
lemma CB2_3_3I1R6Terms_sound (a : Fin 6) :
    (CB2_3_3I1R6Terms a).Encloses (Foundation.entropyTerm (CB2_3_3I1R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_3_3I1R6Certificates_valid
    (CB2_3_3I1R6CertificateIndex a) (CB2_3_3I1R6P_sound a)
lemma CB2_3_3I1R6Entropy_sound : CB2_3_3I1R6Entropy.Encloses (Foundation.finiteEntropy CB2_3_3I1R6Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_3_3I1R6Value CB2_3_3I1R6Terms CB2_3_3I1R6Terms_sound) (by decide +kernel)
lemma CB2_3_3I1R6Mass_sound : CB2_3_3I1R6Mass.Encloses (∑ a, CB2_3_3I1R6Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_3_3I1R6P CB2_3_3I1R6Value CB2_3_3I1R6P_sound) (by decide +kernel)
lemma CB2_3_3I1R6MassTerm_sound : CB2_3_3I1R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_3_3I1R6Value a))) :=
  entropyTerm_zero_ball (CB2_3_3I1R6Mass_sound)
lemma CB2_3_3I1R6H_sound : CB2_3_3I1R6H.Encloses (homogeneousEntropy CB2_3_3I1R6Value) := by
  exact contains_sound (homogeneous_enclosed CB2_3_3I1R6Value CB2_3_3I1R6MassTerm_sound CB2_3_3I1R6Entropy_sound) (by decide +kernel)
lemma CB2_3_3I1R7Certificates_valid :
    CB2_3_3I1R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB2_3_3I1R7P_check : ∀ a : Fin 6, contains (CB2_3_3I1R7Raw a) (CB2_3_3I1R7P a) = true := by
  decide +kernel
lemma CB2_3_3I1R7P_sound (a : Fin 6) :
    (CB2_3_3I1R7P a).Encloses (CB2_3_3I1R7Value a) :=
  contains_sound (CB2_3_3I1R7Raw_sound a) (CB2_3_3I1R7P_check a)
lemma CB2_3_3I1R7Terms_sound (a : Fin 6) :
    (CB2_3_3I1R7Terms a).Encloses (Foundation.entropyTerm (CB2_3_3I1R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_3_3I1R7Certificates_valid
    (CB2_3_3I1R7CertificateIndex a) (CB2_3_3I1R7P_sound a)
lemma CB2_3_3I1R7Entropy_sound : CB2_3_3I1R7Entropy.Encloses (Foundation.finiteEntropy CB2_3_3I1R7Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_3_3I1R7Value CB2_3_3I1R7Terms CB2_3_3I1R7Terms_sound) (by decide +kernel)
lemma CB2_3_3I1R7Mass_sound : CB2_3_3I1R7Mass.Encloses (∑ a, CB2_3_3I1R7Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_3_3I1R7P CB2_3_3I1R7Value CB2_3_3I1R7P_sound) (by decide +kernel)
lemma CB2_3_3I1R7MassTerm_sound : CB2_3_3I1R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_3_3I1R7Value a))) :=
  entropyTerm_zero_ball (CB2_3_3I1R7Mass_sound)
lemma CB2_3_3I1R7H_sound : CB2_3_3I1R7H.Encloses (homogeneousEntropy CB2_3_3I1R7Value) := by
  exact contains_sound (homogeneous_enclosed CB2_3_3I1R7Value CB2_3_3I1R7MassTerm_sound CB2_3_3I1R7Entropy_sound) (by decide +kernel)
lemma CB2_3_3I1R8Certificates_valid :
    CB2_3_3I1R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB2_3_3I1R8P_check : ∀ a : Fin 6, contains (CB2_3_3I1R8Raw a) (CB2_3_3I1R8P a) = true := by
  decide +kernel
lemma CB2_3_3I1R8P_sound (a : Fin 6) :
    (CB2_3_3I1R8P a).Encloses (CB2_3_3I1R8Value a) :=
  contains_sound (CB2_3_3I1R8Raw_sound a) (CB2_3_3I1R8P_check a)
lemma CB2_3_3I1R8Terms_sound (a : Fin 6) :
    (CB2_3_3I1R8Terms a).Encloses (Foundation.entropyTerm (CB2_3_3I1R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_3_3I1R8Certificates_valid
    (CB2_3_3I1R8CertificateIndex a) (CB2_3_3I1R8P_sound a)
lemma CB2_3_3I1R8Entropy_sound : CB2_3_3I1R8Entropy.Encloses (Foundation.finiteEntropy CB2_3_3I1R8Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_3_3I1R8Value CB2_3_3I1R8Terms CB2_3_3I1R8Terms_sound) (by decide +kernel)
lemma CB2_3_3I1R8Mass_sound : CB2_3_3I1R8Mass.Encloses (∑ a, CB2_3_3I1R8Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_3_3I1R8P CB2_3_3I1R8Value CB2_3_3I1R8P_sound) (by decide +kernel)
lemma CB2_3_3I1R8MassTerm_sound : CB2_3_3I1R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_3_3I1R8Value a))) :=
  entropyTerm_zero_ball (CB2_3_3I1R8Mass_sound)
lemma CB2_3_3I1R8H_sound : CB2_3_3I1R8H.Encloses (homogeneousEntropy CB2_3_3I1R8Value) := by
  exact contains_sound (homogeneous_enclosed CB2_3_3I1R8Value CB2_3_3I1R8MassTerm_sound CB2_3_3I1R8Entropy_sound) (by decide +kernel)
lemma CB2_3_3I1R9Certificates_valid :
    CB2_3_3I1R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB2_3_3I1R9P_check : ∀ a : Fin 6, contains (CB2_3_3I1R9Raw a) (CB2_3_3I1R9P a) = true := by
  decide +kernel
lemma CB2_3_3I1R9P_sound (a : Fin 6) :
    (CB2_3_3I1R9P a).Encloses (CB2_3_3I1R9Value a) :=
  contains_sound (CB2_3_3I1R9Raw_sound a) (CB2_3_3I1R9P_check a)
lemma CB2_3_3I1R9Terms_sound (a : Fin 6) :
    (CB2_3_3I1R9Terms a).Encloses (Foundation.entropyTerm (CB2_3_3I1R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_3_3I1R9Certificates_valid
    (CB2_3_3I1R9CertificateIndex a) (CB2_3_3I1R9P_sound a)
lemma CB2_3_3I1R9Entropy_sound : CB2_3_3I1R9Entropy.Encloses (Foundation.finiteEntropy CB2_3_3I1R9Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_3_3I1R9Value CB2_3_3I1R9Terms CB2_3_3I1R9Terms_sound) (by decide +kernel)
lemma CB2_3_3I1R9Mass_sound : CB2_3_3I1R9Mass.Encloses (∑ a, CB2_3_3I1R9Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_3_3I1R9P CB2_3_3I1R9Value CB2_3_3I1R9P_sound) (by decide +kernel)
lemma CB2_3_3I1R9MassTerm_sound : CB2_3_3I1R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_3_3I1R9Value a))) :=
  entropyTerm_zero_ball (CB2_3_3I1R9Mass_sound)
lemma CB2_3_3I1R9H_sound : CB2_3_3I1R9H.Encloses (homogeneousEntropy CB2_3_3I1R9Value) := by
  exact contains_sound (homogeneous_enclosed CB2_3_3I1R9Value CB2_3_3I1R9MassTerm_sound CB2_3_3I1R9Entropy_sound) (by decide +kernel)
lemma CB2_3_3I1R10Certificates_valid :
    CB2_3_3I1R10Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB2_3_3I1R10Terms_sound (a : Fin 6) :
    (CB2_3_3I1R10Terms a).Encloses (Foundation.entropyTerm (CB2_3_3I1R10Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_3_3I1R10Certificates_valid
    (CB2_3_3I1R10CertificateIndex a) (CB2_3_3I1R10P_sound a)
lemma CB2_3_3I1R10Entropy_sound : CB2_3_3I1R10Entropy.Encloses (Foundation.finiteEntropy CB2_3_3I1R10Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_3_3I1R10Value CB2_3_3I1R10Terms CB2_3_3I1R10Terms_sound) (by decide +kernel)
lemma CB2_3_3I1R10Mass_sound : CB2_3_3I1R10Mass.Encloses (∑ a, CB2_3_3I1R10Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_3_3I1R10P CB2_3_3I1R10Value CB2_3_3I1R10P_sound) (by decide +kernel)
lemma CB2_3_3I1R10MassTerm_sound : CB2_3_3I1R10MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_3_3I1R10Value a))) :=
  entropyTerm_zero_ball (CB2_3_3I1R10Mass_sound)
lemma CB2_3_3I1R10H_sound : CB2_3_3I1R10H.Encloses (homogeneousEntropy CB2_3_3I1R10Value) := by
  exact contains_sound (homogeneous_enclosed CB2_3_3I1R10Value CB2_3_3I1R10MassTerm_sound CB2_3_3I1R10Entropy_sound) (by decide +kernel)
lemma CB2_3_3I1R11Certificates_valid :
    CB2_3_3I1R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB2_3_3I1R11P_check : ∀ a : Fin 6, contains (CB2_3_3I1R11Raw a) (CB2_3_3I1R11P a) = true := by
  decide +kernel
lemma CB2_3_3I1R11P_sound (a : Fin 6) :
    (CB2_3_3I1R11P a).Encloses (CB2_3_3I1R11Value a) :=
  contains_sound (CB2_3_3I1R11Raw_sound a) (CB2_3_3I1R11P_check a)
lemma CB2_3_3I1R11Terms_sound (a : Fin 6) :
    (CB2_3_3I1R11Terms a).Encloses (Foundation.entropyTerm (CB2_3_3I1R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_3_3I1R11Certificates_valid
    (CB2_3_3I1R11CertificateIndex a) (CB2_3_3I1R11P_sound a)
lemma CB2_3_3I1R11Entropy_sound : CB2_3_3I1R11Entropy.Encloses (Foundation.finiteEntropy CB2_3_3I1R11Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_3_3I1R11Value CB2_3_3I1R11Terms CB2_3_3I1R11Terms_sound) (by decide +kernel)
lemma CB2_3_3I1R11Mass_sound : CB2_3_3I1R11Mass.Encloses (∑ a, CB2_3_3I1R11Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_3_3I1R11P CB2_3_3I1R11Value CB2_3_3I1R11P_sound) (by decide +kernel)
lemma CB2_3_3I1R11MassTerm_sound : CB2_3_3I1R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_3_3I1R11Value a))) :=
  entropyTerm_zero_ball (CB2_3_3I1R11Mass_sound)
lemma CB2_3_3I1R11H_sound : CB2_3_3I1R11H.Encloses (homogeneousEntropy CB2_3_3I1R11Value) := by
  exact contains_sound (homogeneous_enclosed CB2_3_3I1R11Value CB2_3_3I1R11MassTerm_sound CB2_3_3I1R11Entropy_sound) (by decide +kernel)
lemma CB2_3_3I1R12Certificates_valid :
    CB2_3_3I1R12Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB2_3_3I1R12P_check : ∀ a : Fin 6, contains (CB2_3_3I1R12Raw a) (CB2_3_3I1R12P a) = true := by
  decide +kernel
lemma CB2_3_3I1R12P_sound (a : Fin 6) :
    (CB2_3_3I1R12P a).Encloses (CB2_3_3I1R12Value a) :=
  contains_sound (CB2_3_3I1R12Raw_sound a) (CB2_3_3I1R12P_check a)
lemma CB2_3_3I1R12Terms_sound (a : Fin 6) :
    (CB2_3_3I1R12Terms a).Encloses (Foundation.entropyTerm (CB2_3_3I1R12Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_3_3I1R12Certificates_valid
    (CB2_3_3I1R12CertificateIndex a) (CB2_3_3I1R12P_sound a)
lemma CB2_3_3I1R12Entropy_sound : CB2_3_3I1R12Entropy.Encloses (Foundation.finiteEntropy CB2_3_3I1R12Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_3_3I1R12Value CB2_3_3I1R12Terms CB2_3_3I1R12Terms_sound) (by decide +kernel)
lemma CB2_3_3I1R12Mass_sound : CB2_3_3I1R12Mass.Encloses (∑ a, CB2_3_3I1R12Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_3_3I1R12P CB2_3_3I1R12Value CB2_3_3I1R12P_sound) (by decide +kernel)
lemma CB2_3_3I1R12MassTerm_sound : CB2_3_3I1R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_3_3I1R12Value a))) :=
  entropyTerm_zero_ball (CB2_3_3I1R12Mass_sound)
lemma CB2_3_3I1R12H_sound : CB2_3_3I1R12H.Encloses (homogeneousEntropy CB2_3_3I1R12Value) := by
  exact contains_sound (homogeneous_enclosed CB2_3_3I1R12Value CB2_3_3I1R12MassTerm_sound CB2_3_3I1R12Entropy_sound) (by decide +kernel)
lemma CB2_3_3I1R13Certificates_valid :
    CB2_3_3I1R13Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB2_3_3I1R13P_check : ∀ a : Fin 6, contains (CB2_3_3I1R13Raw a) (CB2_3_3I1R13P a) = true := by
  decide +kernel
lemma CB2_3_3I1R13P_sound (a : Fin 6) :
    (CB2_3_3I1R13P a).Encloses (CB2_3_3I1R13Value a) :=
  contains_sound (CB2_3_3I1R13Raw_sound a) (CB2_3_3I1R13P_check a)
lemma CB2_3_3I1R13Terms_sound (a : Fin 6) :
    (CB2_3_3I1R13Terms a).Encloses (Foundation.entropyTerm (CB2_3_3I1R13Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_3_3I1R13Certificates_valid
    (CB2_3_3I1R13CertificateIndex a) (CB2_3_3I1R13P_sound a)
lemma CB2_3_3I1R13Entropy_sound : CB2_3_3I1R13Entropy.Encloses (Foundation.finiteEntropy CB2_3_3I1R13Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_3_3I1R13Value CB2_3_3I1R13Terms CB2_3_3I1R13Terms_sound) (by decide +kernel)
lemma CB2_3_3I1R13Mass_sound : CB2_3_3I1R13Mass.Encloses (∑ a, CB2_3_3I1R13Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_3_3I1R13P CB2_3_3I1R13Value CB2_3_3I1R13P_sound) (by decide +kernel)
lemma CB2_3_3I1R13MassTerm_sound : CB2_3_3I1R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_3_3I1R13Value a))) :=
  entropyTerm_zero_ball (CB2_3_3I1R13Mass_sound)
lemma CB2_3_3I1R13H_sound : CB2_3_3I1R13H.Encloses (homogeneousEntropy CB2_3_3I1R13Value) := by
  exact contains_sound (homogeneous_enclosed CB2_3_3I1R13Value CB2_3_3I1R13MassTerm_sound CB2_3_3I1R13Entropy_sound) (by decide +kernel)
lemma CB2_3_3I1R14Certificates_valid :
    CB2_3_3I1R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB2_3_3I1R14P_check : ∀ a : Fin 6, contains (CB2_3_3I1R14Raw a) (CB2_3_3I1R14P a) = true := by
  decide +kernel
lemma CB2_3_3I1R14P_sound (a : Fin 6) :
    (CB2_3_3I1R14P a).Encloses (CB2_3_3I1R14Value a) :=
  contains_sound (CB2_3_3I1R14Raw_sound a) (CB2_3_3I1R14P_check a)
lemma CB2_3_3I1R14Terms_sound (a : Fin 6) :
    (CB2_3_3I1R14Terms a).Encloses (Foundation.entropyTerm (CB2_3_3I1R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_3_3I1R14Certificates_valid
    (CB2_3_3I1R14CertificateIndex a) (CB2_3_3I1R14P_sound a)
lemma CB2_3_3I1R14Entropy_sound : CB2_3_3I1R14Entropy.Encloses (Foundation.finiteEntropy CB2_3_3I1R14Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_3_3I1R14Value CB2_3_3I1R14Terms CB2_3_3I1R14Terms_sound) (by decide +kernel)
lemma CB2_3_3I1R14Mass_sound : CB2_3_3I1R14Mass.Encloses (∑ a, CB2_3_3I1R14Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_3_3I1R14P CB2_3_3I1R14Value CB2_3_3I1R14P_sound) (by decide +kernel)
lemma CB2_3_3I1R14MassTerm_sound : CB2_3_3I1R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_3_3I1R14Value a))) :=
  entropyTerm_zero_ball (CB2_3_3I1R14Mass_sound)
lemma CB2_3_3I1R14H_sound : CB2_3_3I1R14H.Encloses (homogeneousEntropy CB2_3_3I1R14Value) := by
  exact contains_sound (homogeneous_enclosed CB2_3_3I1R14Value CB2_3_3I1R14MassTerm_sound CB2_3_3I1R14Entropy_sound) (by decide +kernel)
lemma CB2_3_3I1R15Certificates_valid :
    CB2_3_3I1R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB2_3_3I1R15P_check : ∀ a : Fin 6, contains (CB2_3_3I1R15Raw a) (CB2_3_3I1R15P a) = true := by
  decide +kernel
lemma CB2_3_3I1R15P_sound (a : Fin 6) :
    (CB2_3_3I1R15P a).Encloses (CB2_3_3I1R15Value a) :=
  contains_sound (CB2_3_3I1R15Raw_sound a) (CB2_3_3I1R15P_check a)
lemma CB2_3_3I1R15Terms_sound (a : Fin 6) :
    (CB2_3_3I1R15Terms a).Encloses (Foundation.entropyTerm (CB2_3_3I1R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_3_3I1R15Certificates_valid
    (CB2_3_3I1R15CertificateIndex a) (CB2_3_3I1R15P_sound a)
lemma CB2_3_3I1R15Entropy_sound : CB2_3_3I1R15Entropy.Encloses (Foundation.finiteEntropy CB2_3_3I1R15Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_3_3I1R15Value CB2_3_3I1R15Terms CB2_3_3I1R15Terms_sound) (by decide +kernel)
lemma CB2_3_3I1R15Mass_sound : CB2_3_3I1R15Mass.Encloses (∑ a, CB2_3_3I1R15Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_3_3I1R15P CB2_3_3I1R15Value CB2_3_3I1R15P_sound) (by decide +kernel)
lemma CB2_3_3I1R15MassTerm_sound : CB2_3_3I1R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_3_3I1R15Value a))) :=
  entropyTerm_zero_ball (CB2_3_3I1R15Mass_sound)
lemma CB2_3_3I1R15H_sound : CB2_3_3I1R15H.Encloses (homogeneousEntropy CB2_3_3I1R15Value) := by
  exact contains_sound (homogeneous_enclosed CB2_3_3I1R15Value CB2_3_3I1R15MassTerm_sound CB2_3_3I1R15Entropy_sound) (by decide +kernel)
lemma CB2_3_3I1R16Certificates_valid :
    CB2_3_3I1R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB2_3_3I1R16P_check : ∀ a : Fin 6, contains (CB2_3_3I1R16Raw a) (CB2_3_3I1R16P a) = true := by
  decide +kernel
lemma CB2_3_3I1R16P_sound (a : Fin 6) :
    (CB2_3_3I1R16P a).Encloses (CB2_3_3I1R16Value a) :=
  contains_sound (CB2_3_3I1R16Raw_sound a) (CB2_3_3I1R16P_check a)
lemma CB2_3_3I1R16Terms_sound (a : Fin 6) :
    (CB2_3_3I1R16Terms a).Encloses (Foundation.entropyTerm (CB2_3_3I1R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_3_3I1R16Certificates_valid
    (CB2_3_3I1R16CertificateIndex a) (CB2_3_3I1R16P_sound a)
lemma CB2_3_3I1R16Entropy_sound : CB2_3_3I1R16Entropy.Encloses (Foundation.finiteEntropy CB2_3_3I1R16Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB2_3_3I1R16Value CB2_3_3I1R16Terms CB2_3_3I1R16Terms_sound) (by decide +kernel)
lemma CB2_3_3I1R16Mass_sound : CB2_3_3I1R16Mass.Encloses (∑ a, CB2_3_3I1R16Value a) := by
  exact contains_sound (finSumBall_sound 6 CB2_3_3I1R16P CB2_3_3I1R16Value CB2_3_3I1R16P_sound) (by decide +kernel)
lemma CB2_3_3I1R16MassTerm_sound : CB2_3_3I1R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_3_3I1R16Value a))) :=
  entropyTerm_zero_ball (CB2_3_3I1R16Mass_sound)
lemma CB2_3_3I1R16H_sound : CB2_3_3I1R16H.Encloses (homogeneousEntropy CB2_3_3I1R16Value) := by
  exact contains_sound (homogeneous_enclosed CB2_3_3I1R16Value CB2_3_3I1R16MassTerm_sound CB2_3_3I1R16Entropy_sound) (by decide +kernel)
lemma CB2_3_3I1ResidualEntropies_sound_oai (k : Fin 17) :
    (CB2_3_3I1ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (stageBPriority (shape 2 3 3)) 1 (fun u a => (littleLaw (shape 2 3 3) u ((stageBPriority (shape 2 3 3)) 1) a : ℝ)) k)) := by
  fin_cases k
  · exact CB2_3_3I1R0H_sound
  · exact CB2_3_3I1R1H_sound
  · exact CB2_3_3I1R2H_sound
  · exact CB2_3_3I1R3H_sound
  · exact CB2_3_3I1R4H_sound
  · exact CB2_3_3I1R5H_sound
  · exact CB2_3_3I1R6H_sound
  · exact CB2_3_3I1R7H_sound
  · exact CB2_3_3I1R8H_sound
  · exact CB2_3_3I1R9H_sound
  · exact CB2_3_3I1R10H_sound
  · exact CB2_3_3I1R11H_sound
  · exact CB2_3_3I1R12H_sound
  · exact CB2_3_3I1R13H_sound
  · exact CB2_3_3I1R14H_sound
  · exact CB2_3_3I1R15H_sound
  · exact CB2_3_3I1R16H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB2_3_3I1ResidualEntropies_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB2_3_3I1ResidualEntropies_sound_oai
