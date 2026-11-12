-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I1R2MassTerm_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T14:28:20.970069+00:00
-- url     : https://prove2.me/submissions/2d0a205d-31d6-4368-b51a-297272a7aa61

import Mathlib
import Definitions.Def_OAIQ254M010
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkLog_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_finSumBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_3_2I1R2Raw_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_entropyTerm_ball

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
lemma CB3_3_2I1R2P_check : ∀ a : Fin 6, contains (CB3_3_2I1R2Raw a) (CB3_3_2I1R2P a) = true := by
  decide +kernel
lemma CB3_3_2I1R2P_sound (a : Fin 6) :
    (CB3_3_2I1R2P a).Encloses (CB3_3_2I1R2Value a) :=
  contains_sound (CB3_3_2I1R2Raw_sound a) (CB3_3_2I1R2P_check a)
lemma CB3_3_2I1R2Mass_sound : CB3_3_2I1R2Mass.Encloses (∑ a, CB3_3_2I1R2Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_3_2I1R2P CB3_3_2I1R2Value CB3_3_2I1R2P_sound) (by decide +kernel)
lemma CB3_3_2I1R2MassTermLog_sound : CB3_3_2I1R2MassTermLog.Encloses (Real.log ((∑ a, CB3_3_2I1R2Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB3_3_2I1R2Mass_sound) (w := CB3_3_2I1R2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CB3_3_2I1R2MassTerm_sound_oai : CB3_3_2I1R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_3_2I1R2Value a))) := by
  exact contains_sound (entropyTerm_ball (CB3_3_2I1R2Mass_sound) CB3_3_2I1R2MassTermLog_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I1R2MassTerm_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I1R2MassTerm_sound_oai
