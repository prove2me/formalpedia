-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.native_volume_positive
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:56:30.335529+00:00
-- url     : https://prove2.me/submissions/1cd83dfa-394a-48ed-b5de-90bac89a1a5b

import Mathlib
import Definitions.Def_OAIQ254M005
import Definitions.Def_OAIQ254M007
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_inv_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_mul_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkLog_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_finSumBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_initialDenominatorBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_initialRawBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_nativeS1Ball_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_nativeS2Ball_sound

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

end Ball

end MatrixMultiplication.AllFieldCertificates

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SparseContraction
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.bWeight_val
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

lemma initialDenominatorBall_positive : 0 < initialDenominatorBall.lower := by
  decide +kernel

lemma initialLawBall_sound (s : Shape) (hs : s ∈ sortedInitial) :
    (initialLawBall s).Encloses (initialLaw s : ℝ) := by
  have h := Ball.mul_sound (initialRawBall_sound s hs)
    (Ball.inv_sound initialDenominatorBall_sound initialDenominatorBall_positive)
  simpa only [initialLawBall, initialLaw, hs, ite_true, if_true, Rat.cast_div,
    div_eq_mul_inv, Rat.cast_mul, Rat.cast_inv] using h

end MatrixMultiplication.AllFieldInitialEntropyCertificate

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldVolumeCertificate
open AllFieldParameters AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldTerminalRates
open scoped BigOperators

lemma zeroLeafShape_mem (k : Fin 9) : zeroLeafShape k ∈ sortedInitial := by
  revert k
  decide +kernel

lemma initialZeroShapes : sortedInitial.filter (fun g => !positive g) =
    List.ofFn zeroLeafShape := by
  decide +kernel

lemma nativeS0_eq_sum : S0 = ∑ k : Fin 9,
    (initialLaw (zeroLeafShape k) : ℝ) * initialRate (zeroLeafShape k) := by
  rw [S0, initialZeroShapes, List.map_ofFn, List.sum_ofFn]
  rfl

lemma leafRateBall0_sound : leafRateBall0.Encloses
    (initialRate (zeroLeafShape 0)) := by
  have hc : (Ball.exact (zeroLeafCoefficient 0 : ℚ)).Encloses
      (zeroLeafCoefficient 0 : ℝ) := by
    simpa using Ball.exact_sound (zeroLeafCoefficient 0 : ℚ)
  exact checkLog_sound logTwoBall_sound hc (w := leafLogWitness0) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)

lemma leafRateBall1_sound : leafRateBall1.Encloses
    (initialRate (zeroLeafShape 1)) := by
  have hc : (Ball.exact (zeroLeafCoefficient 1 : ℚ)).Encloses
      (zeroLeafCoefficient 1 : ℝ) := by
    simpa using Ball.exact_sound (zeroLeafCoefficient 1 : ℚ)
  exact checkLog_sound logTwoBall_sound hc (w := leafLogWitness1) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)

lemma leafRateBall2_sound : leafRateBall2.Encloses
    (initialRate (zeroLeafShape 2)) := by
  have hc : (Ball.exact (zeroLeafCoefficient 2 : ℚ)).Encloses
      (zeroLeafCoefficient 2 : ℝ) := by
    simpa using Ball.exact_sound (zeroLeafCoefficient 2 : ℚ)
  exact checkLog_sound logTwoBall_sound hc (w := leafLogWitness2) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)

lemma leafRateBall3_sound : leafRateBall3.Encloses
    (initialRate (zeroLeafShape 3)) := by
  have hc : (Ball.exact (zeroLeafCoefficient 3 : ℚ)).Encloses
      (zeroLeafCoefficient 3 : ℝ) := by
    simpa using Ball.exact_sound (zeroLeafCoefficient 3 : ℚ)
  exact checkLog_sound logTwoBall_sound hc (w := leafLogWitness3) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)

lemma leafRateBall4_sound : leafRateBall4.Encloses
    (initialRate (zeroLeafShape 4)) := by
  have hc : (Ball.exact (zeroLeafCoefficient 4 : ℚ)).Encloses
      (zeroLeafCoefficient 4 : ℝ) := by
    simpa using Ball.exact_sound (zeroLeafCoefficient 4 : ℚ)
  exact checkLog_sound logTwoBall_sound hc (w := leafLogWitness4) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)

lemma leafRateBall5_sound : leafRateBall5.Encloses
    (initialRate (zeroLeafShape 5)) := by
  have hc : (Ball.exact (zeroLeafCoefficient 5 : ℚ)).Encloses
      (zeroLeafCoefficient 5 : ℝ) := by
    simpa using Ball.exact_sound (zeroLeafCoefficient 5 : ℚ)
  exact checkLog_sound logTwoBall_sound hc (w := leafLogWitness5) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)

lemma leafRateBall6_sound : leafRateBall6.Encloses
    (initialRate (zeroLeafShape 6)) := by
  have hc : (Ball.exact (zeroLeafCoefficient 6 : ℚ)).Encloses
      (zeroLeafCoefficient 6 : ℝ) := by
    simpa using Ball.exact_sound (zeroLeafCoefficient 6 : ℚ)
  exact checkLog_sound logTwoBall_sound hc (w := leafLogWitness6) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)

lemma leafRateBall7_sound : leafRateBall7.Encloses
    (initialRate (zeroLeafShape 7)) := by
  have hc : (Ball.exact (zeroLeafCoefficient 7 : ℚ)).Encloses
      (zeroLeafCoefficient 7 : ℝ) := by
    simpa using Ball.exact_sound (zeroLeafCoefficient 7 : ℚ)
  exact checkLog_sound logTwoBall_sound hc (w := leafLogWitness7) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)

lemma leafRateBall8_sound : leafRateBall8.Encloses
    (initialRate (zeroLeafShape 8)) := by
  have hc : (Ball.exact (zeroLeafCoefficient 8 : ℚ)).Encloses
      (zeroLeafCoefficient 8 : ℝ) := by
    simpa using Ball.exact_sound (zeroLeafCoefficient 8 : ℚ)
  exact checkLog_sound logTwoBall_sound hc (w := leafLogWitness8) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)

lemma leafRateBall_sound (k : Fin 9) :
    (leafRateBall k).Encloses (initialRate (zeroLeafShape k)) := by
  fin_cases k
  · exact leafRateBall0_sound
  · exact leafRateBall1_sound
  · exact leafRateBall2_sound
  · exact leafRateBall3_sound
  · exact leafRateBall4_sound
  · exact leafRateBall5_sound
  · exact leafRateBall6_sound
  · exact leafRateBall7_sound
  · exact leafRateBall8_sound

lemma initialVolumeRawBall_sound : initialVolumeRawBall.Encloses S0 := by
  rw [nativeS0_eq_sum]
  apply finSumBall_sound
  intro k
  exact Ball.mul_sound (initialLawBall_sound _ (zeroLeafShape_mem k))
    (leafRateBall_sound k)
theorem nativeS0_enclosed : initialVolumeBall.Encloses S0 := by
  exact contains_sound initialVolumeRawBall_sound (by decide +kernel)
end MatrixMultiplication.AllFieldVolumeCertificate

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_NativeInterior
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
open AllFieldTerminalRates AllFieldVolumeCertificate
lemma nativeSBall_sound : nativeSBall.Encloses S := by
  exact contains_sound (Ball.add_sound (Ball.add_sound nativeS0_enclosed
    nativeS1Ball_sound) nativeS2Ball_sound) (by decide +kernel)

theorem native_volume_positive_oai : 0 < S := by
  have hl := (Ball.bounds nativeSBall_sound).1
  have hp : (0 : ℝ) < nativeSBall.lower := by norm_num [nativeSBall, Ball.lower]
  exact hp.trans_le hl

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.native_volume_positive_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.native_volume_positive_oai
