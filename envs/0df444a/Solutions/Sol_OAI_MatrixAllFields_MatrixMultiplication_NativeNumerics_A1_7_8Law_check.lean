-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A1_7_8Law_check
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T05:55:46.711259+00:00
-- url     : https://prove2.me/submissions/15dd2a67-5d98-47fa-8055-7b2e35353a9e

import Mathlib
import Definitions.Def_OAIQ254M003

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitA1_7_8
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
lemma A1_7_8_below : below (shape 1 7 8) = [
  (shape 0 0 8),
  (shape 0 1 7),
  (shape 0 2 6),
  (shape 0 3 5),
  (shape 0 4 4),
  (shape 0 5 3),
  (shape 0 6 2),
  (shape 0 7 1),
  (shape 1 0 7),
  (shape 1 1 6),
  (shape 1 2 5),
  (shape 1 3 4),
  (shape 1 4 3),
  (shape 1 5 2),
  (shape 1 6 1),
  (shape 1 7 0)] := by decide +kernel
lemma A1_7_8Law_check_0_0_8 : contains (.mul (A1_7_8Raw (shape 0 0 8)) (.inv A1_7_8Den)) (A1_7_8Table (shape 0 0 8)) = true := by decide +kernel
lemma A1_7_8Law_check_0_1_7 : contains (.mul (A1_7_8Raw (shape 0 1 7)) (.inv A1_7_8Den)) (A1_7_8Table (shape 0 1 7)) = true := by decide +kernel
lemma A1_7_8Law_check_0_2_6 : contains (.mul (A1_7_8Raw (shape 0 2 6)) (.inv A1_7_8Den)) (A1_7_8Table (shape 0 2 6)) = true := by decide +kernel
lemma A1_7_8Law_check_0_3_5 : contains (.mul (A1_7_8Raw (shape 0 3 5)) (.inv A1_7_8Den)) (A1_7_8Table (shape 0 3 5)) = true := by decide +kernel
lemma A1_7_8Law_check_0_4_4 : contains (.mul (A1_7_8Raw (shape 0 4 4)) (.inv A1_7_8Den)) (A1_7_8Table (shape 0 4 4)) = true := by decide +kernel
lemma A1_7_8Law_check_0_5_3 : contains (.mul (A1_7_8Raw (shape 0 5 3)) (.inv A1_7_8Den)) (A1_7_8Table (shape 0 5 3)) = true := by decide +kernel
lemma A1_7_8Law_check_0_6_2 : contains (.mul (A1_7_8Raw (shape 0 6 2)) (.inv A1_7_8Den)) (A1_7_8Table (shape 0 6 2)) = true := by decide +kernel
lemma A1_7_8Law_check_0_7_1 : contains (.mul (A1_7_8Raw (shape 0 7 1)) (.inv A1_7_8Den)) (A1_7_8Table (shape 0 7 1)) = true := by decide +kernel
lemma A1_7_8Law_check_1_0_7 : contains (.mul (A1_7_8Raw (shape 1 0 7)) (.inv A1_7_8Den)) (A1_7_8Table (shape 1 0 7)) = true := by decide +kernel
lemma A1_7_8Law_check_1_1_6 : contains (.mul (A1_7_8Raw (shape 1 1 6)) (.inv A1_7_8Den)) (A1_7_8Table (shape 1 1 6)) = true := by decide +kernel
lemma A1_7_8Law_check_1_2_5 : contains (.mul (A1_7_8Raw (shape 1 2 5)) (.inv A1_7_8Den)) (A1_7_8Table (shape 1 2 5)) = true := by decide +kernel
lemma A1_7_8Law_check_1_3_4 : contains (.mul (A1_7_8Raw (shape 1 3 4)) (.inv A1_7_8Den)) (A1_7_8Table (shape 1 3 4)) = true := by decide +kernel
lemma A1_7_8Law_check_1_4_3 : contains (.mul (A1_7_8Raw (shape 1 4 3)) (.inv A1_7_8Den)) (A1_7_8Table (shape 1 4 3)) = true := by decide +kernel
lemma A1_7_8Law_check_1_5_2 : contains (.mul (A1_7_8Raw (shape 1 5 2)) (.inv A1_7_8Den)) (A1_7_8Table (shape 1 5 2)) = true := by decide +kernel
lemma A1_7_8Law_check_1_6_1 : contains (.mul (A1_7_8Raw (shape 1 6 1)) (.inv A1_7_8Den)) (A1_7_8Table (shape 1 6 1)) = true := by decide +kernel
lemma A1_7_8Law_check_1_7_0 : contains (.mul (A1_7_8Raw (shape 1 7 0)) (.inv A1_7_8Den)) (A1_7_8Table (shape 1 7 0)) = true := by decide +kernel
lemma A1_7_8Law_check_oai (u : Shape) (hu : u ∈ below (shape 1 7 8)) :
    contains (.mul (A1_7_8Raw u) (.inv A1_7_8Den)) (A1_7_8Table u) = true := by
  rw [A1_7_8_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A1_7_8Law_check_0_0_8
  · exact A1_7_8Law_check_0_1_7
  · exact A1_7_8Law_check_0_2_6
  · exact A1_7_8Law_check_0_3_5
  · exact A1_7_8Law_check_0_4_4
  · exact A1_7_8Law_check_0_5_3
  · exact A1_7_8Law_check_0_6_2
  · exact A1_7_8Law_check_0_7_1
  · exact A1_7_8Law_check_1_0_7
  · exact A1_7_8Law_check_1_1_6
  · exact A1_7_8Law_check_1_2_5
  · exact A1_7_8Law_check_1_3_4
  · exact A1_7_8Law_check_1_4_3
  · exact A1_7_8Law_check_1_5_2
  · exact A1_7_8Law_check_1_6_1
  · exact A1_7_8Law_check_1_7_0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A1_7_8Law_check_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A1_7_8Law_check_oai
