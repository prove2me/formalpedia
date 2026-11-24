-- Prove2me | solution 1 for GlobalTheory.T.parabolic_induction_contragredient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:02:25.883483+00:00
-- url     : https://prove2.me/submissions/cc69aa2c-7b34-44c2-90ef-73d92d927714

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParabolicInductionContragredient
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfIsIrreducible
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParabolicInductionContragredientStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Glob_inductionContragredient
import Theorems.Thm_GlobalTheory_SmGL_IndDual_inductionContragredient


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.InductionContragredient k := by
  first | exact @GlobalTheory.CompanionTheory.Glob.inductionContragredient | exact GlobalTheory.CompanionTheory.Glob.inductionContragredient | (intros; apply GlobalTheory.CompanionTheory.Glob.inductionContragredient <;> assumption)
end _root_.GlobalTheory.T
