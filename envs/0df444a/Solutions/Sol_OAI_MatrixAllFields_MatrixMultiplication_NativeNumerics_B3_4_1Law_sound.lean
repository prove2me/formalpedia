-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_4_1Law_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:49:24.562351+00:00
-- url     : https://prove2.me/submissions/5d084130-2a88-47b6-82aa-401933394171

import Mathlib
import Definitions.Def_OAIQ254M003
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_inv_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_mul_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B3_4_1Den_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B3_4_1Raw_sound

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal3_4_1
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
lemma B3_4_1_below : below (shape 3 4 1) = [
  (shape 0 3 1),
  (shape 0 4 0),
  (shape 1 2 1),
  (shape 1 3 0),
  (shape 2 1 1),
  (shape 2 2 0),
  (shape 3 0 1),
  (shape 3 1 0)] := by decide +kernel
lemma B3_4_1Den_positive : 0 < B3_4_1Den.lower := by decide +kernel
lemma B3_4_1Law_check_0_3_1 : contains (.mul (B3_4_1Raw (shape 0 3 1)) (.inv B3_4_1Den)) (B3_4_1Table (shape 0 3 1)) = true := by decide +kernel
lemma B3_4_1Law_check_0_4_0 : contains (.mul (B3_4_1Raw (shape 0 4 0)) (.inv B3_4_1Den)) (B3_4_1Table (shape 0 4 0)) = true := by decide +kernel
lemma B3_4_1Law_check_1_2_1 : contains (.mul (B3_4_1Raw (shape 1 2 1)) (.inv B3_4_1Den)) (B3_4_1Table (shape 1 2 1)) = true := by decide +kernel
lemma B3_4_1Law_check_1_3_0 : contains (.mul (B3_4_1Raw (shape 1 3 0)) (.inv B3_4_1Den)) (B3_4_1Table (shape 1 3 0)) = true := by decide +kernel
lemma B3_4_1Law_check_2_1_1 : contains (.mul (B3_4_1Raw (shape 2 1 1)) (.inv B3_4_1Den)) (B3_4_1Table (shape 2 1 1)) = true := by decide +kernel
lemma B3_4_1Law_check_2_2_0 : contains (.mul (B3_4_1Raw (shape 2 2 0)) (.inv B3_4_1Den)) (B3_4_1Table (shape 2 2 0)) = true := by decide +kernel
lemma B3_4_1Law_check_3_0_1 : contains (.mul (B3_4_1Raw (shape 3 0 1)) (.inv B3_4_1Den)) (B3_4_1Table (shape 3 0 1)) = true := by decide +kernel
lemma B3_4_1Law_check_3_1_0 : contains (.mul (B3_4_1Raw (shape 3 1 0)) (.inv B3_4_1Den)) (B3_4_1Table (shape 3 1 0)) = true := by decide +kernel
lemma B3_4_1Law_check (u : Shape) (hu : u ∈ below (shape 3 4 1)) :
    contains (.mul (B3_4_1Raw u) (.inv B3_4_1Den)) (B3_4_1Table u) = true := by
  rw [B3_4_1_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B3_4_1Law_check_0_3_1
  · exact B3_4_1Law_check_0_4_0
  · exact B3_4_1Law_check_1_2_1
  · exact B3_4_1Law_check_1_3_0
  · exact B3_4_1Law_check_2_1_1
  · exact B3_4_1Law_check_2_2_0
  · exact B3_4_1Law_check_3_0_1
  · exact B3_4_1Law_check_3_1_0
lemma B3_4_1Law_sound_oai (u : Shape) :
    (B3_4_1Law u).Encloses (stageBLaw (shape 3 4 1) u : ℝ) := by
  by_cases hu : u ∈ below (shape 3 4 1)
  · have h := contains_sound (Ball.mul_sound (B3_4_1Raw_sound u hu)
      (Ball.inv_sound B3_4_1Den_sound B3_4_1Den_positive)) (B3_4_1Law_check u hu)
    simpa only [B3_4_1Law, hu, ite_true, if_true, stageBLaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [B3_4_1Law, hu, ite_false, if_false, stageBLaw, splitLaw, Rat.cast_zero]
    simpa only [Rat.cast_zero] using Ball.exact_sound 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_4_1Law_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_4_1Law_sound_oai
