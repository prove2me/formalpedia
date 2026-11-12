-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B4_1_3Law_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:50:16.849035+00:00
-- url     : https://prove2.me/submissions/9c28f366-3bf1-469a-b7ad-cf90b7d5a9be

import Mathlib
import Definitions.Def_OAIQ254M003
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_inv_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_mul_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B4_1_3Den_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B4_1_3Raw_sound

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal4_1_3
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
lemma B4_1_3_below : below (shape 4 1 3) = [
  (shape 0 1 3),
  (shape 1 0 3),
  (shape 1 1 2),
  (shape 2 0 2),
  (shape 2 1 1),
  (shape 3 0 1),
  (shape 3 1 0),
  (shape 4 0 0)] := by decide +kernel
lemma B4_1_3Den_positive : 0 < B4_1_3Den.lower := by decide +kernel
lemma B4_1_3Law_check_0_1_3 : contains (.mul (B4_1_3Raw (shape 0 1 3)) (.inv B4_1_3Den)) (B4_1_3Table (shape 0 1 3)) = true := by decide +kernel
lemma B4_1_3Law_check_1_0_3 : contains (.mul (B4_1_3Raw (shape 1 0 3)) (.inv B4_1_3Den)) (B4_1_3Table (shape 1 0 3)) = true := by decide +kernel
lemma B4_1_3Law_check_1_1_2 : contains (.mul (B4_1_3Raw (shape 1 1 2)) (.inv B4_1_3Den)) (B4_1_3Table (shape 1 1 2)) = true := by decide +kernel
lemma B4_1_3Law_check_2_0_2 : contains (.mul (B4_1_3Raw (shape 2 0 2)) (.inv B4_1_3Den)) (B4_1_3Table (shape 2 0 2)) = true := by decide +kernel
lemma B4_1_3Law_check_2_1_1 : contains (.mul (B4_1_3Raw (shape 2 1 1)) (.inv B4_1_3Den)) (B4_1_3Table (shape 2 1 1)) = true := by decide +kernel
lemma B4_1_3Law_check_3_0_1 : contains (.mul (B4_1_3Raw (shape 3 0 1)) (.inv B4_1_3Den)) (B4_1_3Table (shape 3 0 1)) = true := by decide +kernel
lemma B4_1_3Law_check_3_1_0 : contains (.mul (B4_1_3Raw (shape 3 1 0)) (.inv B4_1_3Den)) (B4_1_3Table (shape 3 1 0)) = true := by decide +kernel
lemma B4_1_3Law_check_4_0_0 : contains (.mul (B4_1_3Raw (shape 4 0 0)) (.inv B4_1_3Den)) (B4_1_3Table (shape 4 0 0)) = true := by decide +kernel
lemma B4_1_3Law_check (u : Shape) (hu : u ∈ below (shape 4 1 3)) :
    contains (.mul (B4_1_3Raw u) (.inv B4_1_3Den)) (B4_1_3Table u) = true := by
  rw [B4_1_3_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B4_1_3Law_check_0_1_3
  · exact B4_1_3Law_check_1_0_3
  · exact B4_1_3Law_check_1_1_2
  · exact B4_1_3Law_check_2_0_2
  · exact B4_1_3Law_check_2_1_1
  · exact B4_1_3Law_check_3_0_1
  · exact B4_1_3Law_check_3_1_0
  · exact B4_1_3Law_check_4_0_0
lemma B4_1_3Law_sound_oai (u : Shape) :
    (B4_1_3Law u).Encloses (stageBLaw (shape 4 1 3) u : ℝ) := by
  by_cases hu : u ∈ below (shape 4 1 3)
  · have h := contains_sound (Ball.mul_sound (B4_1_3Raw_sound u hu)
      (Ball.inv_sound B4_1_3Den_sound B4_1_3Den_positive)) (B4_1_3Law_check u hu)
    simpa only [B4_1_3Law, hu, ite_true, if_true, stageBLaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [B4_1_3Law, hu, ite_false, if_false, stageBLaw, splitLaw, Rat.cast_zero]
    simpa only [Rat.cast_zero] using Ball.exact_sound 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B4_1_3Law_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B4_1_3Law_sound_oai
