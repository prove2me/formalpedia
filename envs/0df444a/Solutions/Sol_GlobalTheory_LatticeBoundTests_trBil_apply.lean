-- Prove2me | solution 1 for GlobalTheory.LatticeBoundTests.trBil_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:46:34.194804+00:00
-- url     : https://prove2.me/submissions/b9ae4d27-6594-4606-bc94-23c5797fd87c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_PremisesInhabited

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LatticeBoundTests
open NumberField
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
omit [IsCMField E]
namespace GlobalTheory.LatticeBoundTests
theorem _root_.solution (x y : 𝓞 E) :
    trBil E x y = ∑ σ : E →+* ℂ, (σ (x : E) * starRingEnd ℂ (σ (y : E))).re := rfl
end GlobalTheory.LatticeBoundTests
