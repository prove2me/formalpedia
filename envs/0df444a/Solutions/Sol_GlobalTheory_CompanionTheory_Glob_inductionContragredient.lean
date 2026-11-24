-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Glob.inductionContragredient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:53:08.275961+00:00
-- url     : https://prove2.me/submissions/eafbca83-4137-466b-866f-8077f98a8d22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfIsIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_InductionContragredient
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParabolicInductionContragredient
import Theorems.Thm_GlobalTheory_SmGL_IndDual_inductionContragredient


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Glob
namespace GlobalTheory.CompanionTheory.Glob
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.InductionContragredient k :=
  GlobalTheory.SmGL.IndDual.inductionContragredient
end GlobalTheory.CompanionTheory.Glob
