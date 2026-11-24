-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.CptModel.isCptGen_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:17:07.17044+00:00
-- url     : https://prove2.me/submissions/70269978-8258-4baf-962f-6d6dbe2fabc8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsCptGen
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InjectiveOfIsCptGen
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CptModel_isCptGen_fractionRing

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
theorem _root_.solution : IsCptGen (pt (algebraMap ℤ ℚ)) := isCptGen_fractionRing
end GlobalTheory.CompanionTheory.Ar.CptModel
