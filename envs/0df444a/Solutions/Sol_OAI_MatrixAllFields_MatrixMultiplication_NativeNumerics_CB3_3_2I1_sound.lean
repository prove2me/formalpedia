-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I1_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T14:28:34.370549+00:00
-- url     : https://prove2.me/submissions/4834d374-d260-4327-9a66-1346ab31a75e

import Mathlib
import Definitions.Def_OAIQ254M010
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_mul_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkLog_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_finSumBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_CompactCertificate_entropyLookup_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_3_2I1PairH_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_3_2I1R0P_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_3_2I1R10H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_3_2I1R11H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_3_2I1R12H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_3_2I1R13H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_3_2I1R14H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_3_2I1R15H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_3_2I1R16H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_3_2I1R1H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_3_2I1R2MassTerm_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_3_2I1R2Raw_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_3_2I1R3H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_3_2I1R4H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_3_2I1R5H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_3_2I1R6Entropy_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_3_2I1R6MassTerm_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_3_2I1R7Raw_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_3_2I1R7Terms_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_3_2I1R8Raw_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_3_2I1R8Terms_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_3_2I1R9Raw_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_3_2I1Singleton_sound
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

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB3_3_2I1
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
lemma CB3_3_2I1R0Certificates_valid :
    CB3_3_2I1R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB3_3_2I1R0Terms_sound (a : Fin 6) :
    (CB3_3_2I1R0Terms a).Encloses (Foundation.entropyTerm (CB3_3_2I1R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_3_2I1R0Certificates_valid
    (CB3_3_2I1R0CertificateIndex a) (CB3_3_2I1R0P_sound a)
lemma CB3_3_2I1R0Entropy_sound : CB3_3_2I1R0Entropy.Encloses (Foundation.finiteEntropy CB3_3_2I1R0Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_3_2I1R0Value CB3_3_2I1R0Terms CB3_3_2I1R0Terms_sound) (by decide +kernel)
lemma CB3_3_2I1R0Mass_sound : CB3_3_2I1R0Mass.Encloses (∑ a, CB3_3_2I1R0Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_3_2I1R0P CB3_3_2I1R0Value CB3_3_2I1R0P_sound) (by decide +kernel)
lemma CB3_3_2I1R0MassTermLog_sound : CB3_3_2I1R0MassTermLog.Encloses (Real.log ((∑ a, CB3_3_2I1R0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB3_3_2I1R0Mass_sound) (w := CB3_3_2I1R0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CB3_3_2I1R0MassTerm_sound : CB3_3_2I1R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_3_2I1R0Value a))) := by
  exact contains_sound (entropyTerm_ball (CB3_3_2I1R0Mass_sound) CB3_3_2I1R0MassTermLog_sound) (by decide +kernel)
lemma CB3_3_2I1R0H_sound : CB3_3_2I1R0H.Encloses (homogeneousEntropy CB3_3_2I1R0Value) := by
  exact contains_sound (homogeneous_enclosed CB3_3_2I1R0Value CB3_3_2I1R0MassTerm_sound CB3_3_2I1R0Entropy_sound) (by decide +kernel)
lemma CB3_3_2I1R2Certificates_valid :
    CB3_3_2I1R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB3_3_2I1R2P_check : ∀ a : Fin 6, contains (CB3_3_2I1R2Raw a) (CB3_3_2I1R2P a) = true := by
  decide +kernel
lemma CB3_3_2I1R2P_sound (a : Fin 6) :
    (CB3_3_2I1R2P a).Encloses (CB3_3_2I1R2Value a) :=
  contains_sound (CB3_3_2I1R2Raw_sound a) (CB3_3_2I1R2P_check a)
lemma CB3_3_2I1R2Terms_sound (a : Fin 6) :
    (CB3_3_2I1R2Terms a).Encloses (Foundation.entropyTerm (CB3_3_2I1R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_3_2I1R2Certificates_valid
    (CB3_3_2I1R2CertificateIndex a) (CB3_3_2I1R2P_sound a)
lemma CB3_3_2I1R2Entropy_sound : CB3_3_2I1R2Entropy.Encloses (Foundation.finiteEntropy CB3_3_2I1R2Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_3_2I1R2Value CB3_3_2I1R2Terms CB3_3_2I1R2Terms_sound) (by decide +kernel)
lemma CB3_3_2I1R2H_sound : CB3_3_2I1R2H.Encloses (homogeneousEntropy CB3_3_2I1R2Value) := by
  exact contains_sound (homogeneous_enclosed CB3_3_2I1R2Value CB3_3_2I1R2MassTerm_sound CB3_3_2I1R2Entropy_sound) (by decide +kernel)
lemma CB3_3_2I1R6H_sound : CB3_3_2I1R6H.Encloses (homogeneousEntropy CB3_3_2I1R6Value) := by
  exact contains_sound (homogeneous_enclosed CB3_3_2I1R6Value CB3_3_2I1R6MassTerm_sound CB3_3_2I1R6Entropy_sound) (by decide +kernel)
lemma CB3_3_2I1R7P_check : ∀ a : Fin 6, contains (CB3_3_2I1R7Raw a) (CB3_3_2I1R7P a) = true := by
  decide +kernel
lemma CB3_3_2I1R7P_sound (a : Fin 6) :
    (CB3_3_2I1R7P a).Encloses (CB3_3_2I1R7Value a) :=
  contains_sound (CB3_3_2I1R7Raw_sound a) (CB3_3_2I1R7P_check a)
lemma CB3_3_2I1R7Entropy_sound : CB3_3_2I1R7Entropy.Encloses (Foundation.finiteEntropy CB3_3_2I1R7Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_3_2I1R7Value CB3_3_2I1R7Terms CB3_3_2I1R7Terms_sound) (by decide +kernel)
lemma CB3_3_2I1R7Mass_sound : CB3_3_2I1R7Mass.Encloses (∑ a, CB3_3_2I1R7Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_3_2I1R7P CB3_3_2I1R7Value CB3_3_2I1R7P_sound) (by decide +kernel)
lemma CB3_3_2I1R7MassTerm_sound : CB3_3_2I1R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_3_2I1R7Value a))) :=
  entropyTerm_zero_ball (CB3_3_2I1R7Mass_sound)
lemma CB3_3_2I1R7H_sound : CB3_3_2I1R7H.Encloses (homogeneousEntropy CB3_3_2I1R7Value) := by
  exact contains_sound (homogeneous_enclosed CB3_3_2I1R7Value CB3_3_2I1R7MassTerm_sound CB3_3_2I1R7Entropy_sound) (by decide +kernel)
lemma CB3_3_2I1R8P_check : ∀ a : Fin 6, contains (CB3_3_2I1R8Raw a) (CB3_3_2I1R8P a) = true := by
  decide +kernel
lemma CB3_3_2I1R8P_sound (a : Fin 6) :
    (CB3_3_2I1R8P a).Encloses (CB3_3_2I1R8Value a) :=
  contains_sound (CB3_3_2I1R8Raw_sound a) (CB3_3_2I1R8P_check a)
lemma CB3_3_2I1R8Entropy_sound : CB3_3_2I1R8Entropy.Encloses (Foundation.finiteEntropy CB3_3_2I1R8Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_3_2I1R8Value CB3_3_2I1R8Terms CB3_3_2I1R8Terms_sound) (by decide +kernel)
lemma CB3_3_2I1R8Mass_sound : CB3_3_2I1R8Mass.Encloses (∑ a, CB3_3_2I1R8Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_3_2I1R8P CB3_3_2I1R8Value CB3_3_2I1R8P_sound) (by decide +kernel)
lemma CB3_3_2I1R8MassTerm_sound : CB3_3_2I1R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_3_2I1R8Value a))) :=
  entropyTerm_zero_ball (CB3_3_2I1R8Mass_sound)
lemma CB3_3_2I1R8H_sound : CB3_3_2I1R8H.Encloses (homogeneousEntropy CB3_3_2I1R8Value) := by
  exact contains_sound (homogeneous_enclosed CB3_3_2I1R8Value CB3_3_2I1R8MassTerm_sound CB3_3_2I1R8Entropy_sound) (by decide +kernel)
lemma CB3_3_2I1R9Certificates_valid :
    CB3_3_2I1R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB3_3_2I1R9P_check : ∀ a : Fin 6, contains (CB3_3_2I1R9Raw a) (CB3_3_2I1R9P a) = true := by
  decide +kernel
lemma CB3_3_2I1R9P_sound (a : Fin 6) :
    (CB3_3_2I1R9P a).Encloses (CB3_3_2I1R9Value a) :=
  contains_sound (CB3_3_2I1R9Raw_sound a) (CB3_3_2I1R9P_check a)
lemma CB3_3_2I1R9Terms_sound (a : Fin 6) :
    (CB3_3_2I1R9Terms a).Encloses (Foundation.entropyTerm (CB3_3_2I1R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_3_2I1R9Certificates_valid
    (CB3_3_2I1R9CertificateIndex a) (CB3_3_2I1R9P_sound a)
lemma CB3_3_2I1R9Entropy_sound : CB3_3_2I1R9Entropy.Encloses (Foundation.finiteEntropy CB3_3_2I1R9Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_3_2I1R9Value CB3_3_2I1R9Terms CB3_3_2I1R9Terms_sound) (by decide +kernel)
lemma CB3_3_2I1R9Mass_sound : CB3_3_2I1R9Mass.Encloses (∑ a, CB3_3_2I1R9Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_3_2I1R9P CB3_3_2I1R9Value CB3_3_2I1R9P_sound) (by decide +kernel)
lemma CB3_3_2I1R9MassTerm_sound : CB3_3_2I1R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_3_2I1R9Value a))) :=
  entropyTerm_zero_ball (CB3_3_2I1R9Mass_sound)
lemma CB3_3_2I1R9H_sound : CB3_3_2I1R9H.Encloses (homogeneousEntropy CB3_3_2I1R9Value) := by
  exact contains_sound (homogeneous_enclosed CB3_3_2I1R9Value CB3_3_2I1R9MassTerm_sound CB3_3_2I1R9Entropy_sound) (by decide +kernel)
lemma CB3_3_2I1ResidualEntropies_sound (k : Fin 17) :
    (CB3_3_2I1ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 3 3 2)) (fun u => (stageBLaw (shape 3 3 2) u : ℝ)) (stageBPriority (shape 3 3 2)) 1 (fun u a => (littleLaw (shape 3 3 2) u ((stageBPriority (shape 3 3 2)) 1) a : ℝ)) k)) := by
  fin_cases k
  · exact CB3_3_2I1R0H_sound
  · exact CB3_3_2I1R1H_sound
  · exact CB3_3_2I1R2H_sound
  · exact CB3_3_2I1R3H_sound
  · exact CB3_3_2I1R4H_sound
  · exact CB3_3_2I1R5H_sound
  · exact CB3_3_2I1R6H_sound
  · exact CB3_3_2I1R7H_sound
  · exact CB3_3_2I1R8H_sound
  · exact CB3_3_2I1R9H_sound
  · exact CB3_3_2I1R10H_sound
  · exact CB3_3_2I1R11H_sound
  · exact CB3_3_2I1R12H_sound
  · exact CB3_3_2I1R13H_sound
  · exact CB3_3_2I1R14H_sound
  · exact CB3_3_2I1R15H_sound
  · exact CB3_3_2I1R16H_sound
lemma CB3_3_2I1Group_sound : CB3_3_2I1Group.Encloses
    (groupedEntropy (below (shape 3 3 2)) (fun u => (stageBLaw (shape 3 3 2) u : ℝ)) (stageBPriority (shape 3 3 2)) 1 (fun u a => (littleLaw (shape 3 3 2) u ((stageBPriority (shape 3 3 2)) 1) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CB3_3_2I1Singleton_sound
    (finSumBall_sound 17 CB3_3_2I1ResidualEntropies _ CB3_3_2I1ResidualEntropies_sound)) (by decide +kernel)

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
lemma CB3_3_2I1_sound_oai : CB3_3_2I1H.Encloses (stageBCapacity (shape 3 3 2) 1) := by
  have hb := contains_sound (Ball.add_sound CB3_3_2I1PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CB3_3_2I1Group_sound)))
    (show contains (.add CB3_3_2I1PairH (.neg (.mul (.exact 2) CB3_3_2I1Group))) CB3_3_2I1H = true by decide +kernel)
  unfold CB3_3_2I1PairValue at hb
  simpa only [stageBCapacity, nativeCapacity,
    show (1 : Fin 3) ≠ 0 by decide, ite_false, if_false, sub_eq_add_neg] using hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I1_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I1_sound_oai
