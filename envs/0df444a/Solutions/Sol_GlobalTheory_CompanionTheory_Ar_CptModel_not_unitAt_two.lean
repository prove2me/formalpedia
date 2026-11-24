-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.CptModel.not_unitAt_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:17:12.079007+00:00
-- url     : https://prove2.me/submissions/f21582ad-485f-44cd-a35e-6e0dc7a72a99

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsCptGen
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InjectiveOfIsCptGen
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CptModel_half_notMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.CptModel
open AlgebraicGeometry CategoryTheory
namespace GlobalTheory.CompanionTheory.Ar.CptModel
theorem _root_.solution : ¬ unitAt _ two (2 : ℚ) := fun h => half_notMem h.2.2
end GlobalTheory.CompanionTheory.Ar.CptModel
