-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB1_2_5I2R2Mass_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T14:23:21.174596+00:00
-- url     : https://prove2.me/submissions/a21a0485-98f8-4189-a28c-37bbedd27c39

import Mathlib
import Definitions.Def_OAIQ254M010
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_finSumBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB1_2_5I2R2Raw_sound

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB1_2_5I2
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
lemma CB1_2_5I2R2P_check : ∀ a : Fin 6, contains (CB1_2_5I2R2Raw a) (CB1_2_5I2R2P a) = true := by
  decide +kernel
lemma CB1_2_5I2R2P_sound (a : Fin 6) :
    (CB1_2_5I2R2P a).Encloses (CB1_2_5I2R2Value a) :=
  contains_sound (CB1_2_5I2R2Raw_sound a) (CB1_2_5I2R2P_check a)
lemma CB1_2_5I2R2Mass_sound_oai : CB1_2_5I2R2Mass.Encloses (∑ a, CB1_2_5I2R2Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_2_5I2R2P CB1_2_5I2R2Value CB1_2_5I2R2P_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB1_2_5I2R2Mass_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB1_2_5I2R2Mass_sound_oai
