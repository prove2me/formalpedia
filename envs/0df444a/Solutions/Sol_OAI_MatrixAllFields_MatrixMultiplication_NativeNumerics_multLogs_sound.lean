-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.multLogs_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:23:31.586327+00:00
-- url     : https://prove2.me/submissions/84a83cbc-5feb-4450-a336-886f69e98b16

import Mathlib
import Definitions.Def_OAIQ254M011
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkLog_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound

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

end Ball

end MatrixMultiplication.AllFieldCertificates

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SparseContraction
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
lemma logN1_sound : logN1.Encloses (Real.log ((1 : ℝ))) := by
  exact log_exact_one_ball ((by convert Ball.exact_sound (1 : ℚ) using 1; norm_num))
lemma logN2_sound : logN2.Encloses (Real.log ((2 : ℝ))) := by
  exact checkLog_sound logTwoBall_sound ((by convert Ball.exact_sound (2 : ℚ) using 1; norm_num)) (w := logN2Witness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma logN4_sound : logN4.Encloses (Real.log ((4 : ℝ))) := by
  exact checkLog_sound logTwoBall_sound ((by convert Ball.exact_sound (4 : ℚ) using 1; norm_num)) (w := logN4Witness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma logN10_sound : logN10.Encloses (Real.log ((10 : ℝ))) := by
  exact checkLog_sound logTwoBall_sound ((by convert Ball.exact_sound (10 : ℚ) using 1; norm_num)) (w := logN10Witness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma logN20_sound : logN20.Encloses (Real.log ((20 : ℝ))) := by
  exact checkLog_sound logTwoBall_sound ((by convert Ball.exact_sound (20 : ℚ) using 1; norm_num)) (w := logN20Witness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma logN25_sound : logN25.Encloses (Real.log ((25 : ℝ))) := by
  exact checkLog_sound logTwoBall_sound ((by convert Ball.exact_sound (25 : ℚ) using 1; norm_num)) (w := logN25Witness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma logN50_sound : logN50.Encloses (Real.log ((50 : ℝ))) := by
  exact checkLog_sound logTwoBall_sound ((by convert Ball.exact_sound (50 : ℚ) using 1; norm_num)) (w := logN50Witness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma logN100_sound : logN100.Encloses (Real.log ((100 : ℝ))) := by
  exact checkLog_sound logTwoBall_sound ((by convert Ball.exact_sound (100 : ℚ) using 1; norm_num)) (w := logN100Witness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma logN250_sound : logN250.Encloses (Real.log ((250 : ℝ))) := by
  exact checkLog_sound logTwoBall_sound ((by convert Ball.exact_sound (250 : ℚ) using 1; norm_num)) (w := logN250Witness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma logN625_sound : logN625.Encloses (Real.log ((625 : ℝ))) := by
  exact checkLog_sound logTwoBall_sound ((by convert Ball.exact_sound (625 : ℚ) using 1; norm_num)) (w := logN625Witness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma multLogs_sound_oai (a : PairSlot) :
    (multLogs a).Encloses (Real.log (AllFieldParameters.multiplicity a.1 * AllFieldParameters.multiplicity a.2 : ℕ)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · apply forall_fin6
    · have he : AllFieldParameters.multiplicity 0 * AllFieldParameters.multiplicity 0 = 1 := by decide +kernel
      change (multLogs (0,0)).Encloses (Real.log (AllFieldParameters.multiplicity 0 * AllFieldParameters.multiplicity 0 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN1_sound
    · have he : AllFieldParameters.multiplicity 0 * AllFieldParameters.multiplicity 1 = 10 := by decide +kernel
      change (multLogs (0,1)).Encloses (Real.log (AllFieldParameters.multiplicity 0 * AllFieldParameters.multiplicity 1 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN10_sound
    · have he : AllFieldParameters.multiplicity 0 * AllFieldParameters.multiplicity 2 = 25 := by decide +kernel
      change (multLogs (0,2)).Encloses (Real.log (AllFieldParameters.multiplicity 0 * AllFieldParameters.multiplicity 2 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN25_sound
    · have he : AllFieldParameters.multiplicity 0 * AllFieldParameters.multiplicity 3 = 2 := by decide +kernel
      change (multLogs (0,3)).Encloses (Real.log (AllFieldParameters.multiplicity 0 * AllFieldParameters.multiplicity 3 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN2_sound
    · have he : AllFieldParameters.multiplicity 0 * AllFieldParameters.multiplicity 4 = 10 := by decide +kernel
      change (multLogs (0,4)).Encloses (Real.log (AllFieldParameters.multiplicity 0 * AllFieldParameters.multiplicity 4 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN10_sound
    · have he : AllFieldParameters.multiplicity 0 * AllFieldParameters.multiplicity 5 = 1 := by decide +kernel
      change (multLogs (0,5)).Encloses (Real.log (AllFieldParameters.multiplicity 0 * AllFieldParameters.multiplicity 5 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN1_sound
  · apply forall_fin6
    · have he : AllFieldParameters.multiplicity 1 * AllFieldParameters.multiplicity 0 = 10 := by decide +kernel
      change (multLogs (1,0)).Encloses (Real.log (AllFieldParameters.multiplicity 1 * AllFieldParameters.multiplicity 0 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN10_sound
    · have he : AllFieldParameters.multiplicity 1 * AllFieldParameters.multiplicity 1 = 100 := by decide +kernel
      change (multLogs (1,1)).Encloses (Real.log (AllFieldParameters.multiplicity 1 * AllFieldParameters.multiplicity 1 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN100_sound
    · have he : AllFieldParameters.multiplicity 1 * AllFieldParameters.multiplicity 2 = 250 := by decide +kernel
      change (multLogs (1,2)).Encloses (Real.log (AllFieldParameters.multiplicity 1 * AllFieldParameters.multiplicity 2 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN250_sound
    · have he : AllFieldParameters.multiplicity 1 * AllFieldParameters.multiplicity 3 = 20 := by decide +kernel
      change (multLogs (1,3)).Encloses (Real.log (AllFieldParameters.multiplicity 1 * AllFieldParameters.multiplicity 3 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN20_sound
    · have he : AllFieldParameters.multiplicity 1 * AllFieldParameters.multiplicity 4 = 100 := by decide +kernel
      change (multLogs (1,4)).Encloses (Real.log (AllFieldParameters.multiplicity 1 * AllFieldParameters.multiplicity 4 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN100_sound
    · have he : AllFieldParameters.multiplicity 1 * AllFieldParameters.multiplicity 5 = 10 := by decide +kernel
      change (multLogs (1,5)).Encloses (Real.log (AllFieldParameters.multiplicity 1 * AllFieldParameters.multiplicity 5 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN10_sound
  · apply forall_fin6
    · have he : AllFieldParameters.multiplicity 2 * AllFieldParameters.multiplicity 0 = 25 := by decide +kernel
      change (multLogs (2,0)).Encloses (Real.log (AllFieldParameters.multiplicity 2 * AllFieldParameters.multiplicity 0 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN25_sound
    · have he : AllFieldParameters.multiplicity 2 * AllFieldParameters.multiplicity 1 = 250 := by decide +kernel
      change (multLogs (2,1)).Encloses (Real.log (AllFieldParameters.multiplicity 2 * AllFieldParameters.multiplicity 1 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN250_sound
    · have he : AllFieldParameters.multiplicity 2 * AllFieldParameters.multiplicity 2 = 625 := by decide +kernel
      change (multLogs (2,2)).Encloses (Real.log (AllFieldParameters.multiplicity 2 * AllFieldParameters.multiplicity 2 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN625_sound
    · have he : AllFieldParameters.multiplicity 2 * AllFieldParameters.multiplicity 3 = 50 := by decide +kernel
      change (multLogs (2,3)).Encloses (Real.log (AllFieldParameters.multiplicity 2 * AllFieldParameters.multiplicity 3 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN50_sound
    · have he : AllFieldParameters.multiplicity 2 * AllFieldParameters.multiplicity 4 = 250 := by decide +kernel
      change (multLogs (2,4)).Encloses (Real.log (AllFieldParameters.multiplicity 2 * AllFieldParameters.multiplicity 4 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN250_sound
    · have he : AllFieldParameters.multiplicity 2 * AllFieldParameters.multiplicity 5 = 25 := by decide +kernel
      change (multLogs (2,5)).Encloses (Real.log (AllFieldParameters.multiplicity 2 * AllFieldParameters.multiplicity 5 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN25_sound
  · apply forall_fin6
    · have he : AllFieldParameters.multiplicity 3 * AllFieldParameters.multiplicity 0 = 2 := by decide +kernel
      change (multLogs (3,0)).Encloses (Real.log (AllFieldParameters.multiplicity 3 * AllFieldParameters.multiplicity 0 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN2_sound
    · have he : AllFieldParameters.multiplicity 3 * AllFieldParameters.multiplicity 1 = 20 := by decide +kernel
      change (multLogs (3,1)).Encloses (Real.log (AllFieldParameters.multiplicity 3 * AllFieldParameters.multiplicity 1 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN20_sound
    · have he : AllFieldParameters.multiplicity 3 * AllFieldParameters.multiplicity 2 = 50 := by decide +kernel
      change (multLogs (3,2)).Encloses (Real.log (AllFieldParameters.multiplicity 3 * AllFieldParameters.multiplicity 2 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN50_sound
    · have he : AllFieldParameters.multiplicity 3 * AllFieldParameters.multiplicity 3 = 4 := by decide +kernel
      change (multLogs (3,3)).Encloses (Real.log (AllFieldParameters.multiplicity 3 * AllFieldParameters.multiplicity 3 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN4_sound
    · have he : AllFieldParameters.multiplicity 3 * AllFieldParameters.multiplicity 4 = 20 := by decide +kernel
      change (multLogs (3,4)).Encloses (Real.log (AllFieldParameters.multiplicity 3 * AllFieldParameters.multiplicity 4 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN20_sound
    · have he : AllFieldParameters.multiplicity 3 * AllFieldParameters.multiplicity 5 = 2 := by decide +kernel
      change (multLogs (3,5)).Encloses (Real.log (AllFieldParameters.multiplicity 3 * AllFieldParameters.multiplicity 5 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN2_sound
  · apply forall_fin6
    · have he : AllFieldParameters.multiplicity 4 * AllFieldParameters.multiplicity 0 = 10 := by decide +kernel
      change (multLogs (4,0)).Encloses (Real.log (AllFieldParameters.multiplicity 4 * AllFieldParameters.multiplicity 0 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN10_sound
    · have he : AllFieldParameters.multiplicity 4 * AllFieldParameters.multiplicity 1 = 100 := by decide +kernel
      change (multLogs (4,1)).Encloses (Real.log (AllFieldParameters.multiplicity 4 * AllFieldParameters.multiplicity 1 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN100_sound
    · have he : AllFieldParameters.multiplicity 4 * AllFieldParameters.multiplicity 2 = 250 := by decide +kernel
      change (multLogs (4,2)).Encloses (Real.log (AllFieldParameters.multiplicity 4 * AllFieldParameters.multiplicity 2 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN250_sound
    · have he : AllFieldParameters.multiplicity 4 * AllFieldParameters.multiplicity 3 = 20 := by decide +kernel
      change (multLogs (4,3)).Encloses (Real.log (AllFieldParameters.multiplicity 4 * AllFieldParameters.multiplicity 3 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN20_sound
    · have he : AllFieldParameters.multiplicity 4 * AllFieldParameters.multiplicity 4 = 100 := by decide +kernel
      change (multLogs (4,4)).Encloses (Real.log (AllFieldParameters.multiplicity 4 * AllFieldParameters.multiplicity 4 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN100_sound
    · have he : AllFieldParameters.multiplicity 4 * AllFieldParameters.multiplicity 5 = 10 := by decide +kernel
      change (multLogs (4,5)).Encloses (Real.log (AllFieldParameters.multiplicity 4 * AllFieldParameters.multiplicity 5 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN10_sound
  · apply forall_fin6
    · have he : AllFieldParameters.multiplicity 5 * AllFieldParameters.multiplicity 0 = 1 := by decide +kernel
      change (multLogs (5,0)).Encloses (Real.log (AllFieldParameters.multiplicity 5 * AllFieldParameters.multiplicity 0 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN1_sound
    · have he : AllFieldParameters.multiplicity 5 * AllFieldParameters.multiplicity 1 = 10 := by decide +kernel
      change (multLogs (5,1)).Encloses (Real.log (AllFieldParameters.multiplicity 5 * AllFieldParameters.multiplicity 1 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN10_sound
    · have he : AllFieldParameters.multiplicity 5 * AllFieldParameters.multiplicity 2 = 25 := by decide +kernel
      change (multLogs (5,2)).Encloses (Real.log (AllFieldParameters.multiplicity 5 * AllFieldParameters.multiplicity 2 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN25_sound
    · have he : AllFieldParameters.multiplicity 5 * AllFieldParameters.multiplicity 3 = 2 := by decide +kernel
      change (multLogs (5,3)).Encloses (Real.log (AllFieldParameters.multiplicity 5 * AllFieldParameters.multiplicity 3 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN2_sound
    · have he : AllFieldParameters.multiplicity 5 * AllFieldParameters.multiplicity 4 = 10 := by decide +kernel
      change (multLogs (5,4)).Encloses (Real.log (AllFieldParameters.multiplicity 5 * AllFieldParameters.multiplicity 4 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN10_sound
    · have he : AllFieldParameters.multiplicity 5 * AllFieldParameters.multiplicity 5 = 1 := by decide +kernel
      change (multLogs (5,5)).Encloses (Real.log (AllFieldParameters.multiplicity 5 * AllFieldParameters.multiplicity 5 : ℕ))
      rw [he]
      simpa only [multLogs, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_one] using logN1_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.multLogs_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.multLogs_sound_oai
