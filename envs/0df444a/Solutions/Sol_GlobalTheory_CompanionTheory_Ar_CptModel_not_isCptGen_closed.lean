-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.CptModel.not_isCptGen_closed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:31:31.287083+00:00
-- url     : https://prove2.me/submissions/d7b8f4d5-207d-434a-84a4-3db329bf5c6d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsCptGen
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InjectiveOfIsCptGen
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CptModel_injective_of_isCptGen

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
theorem _root_.solution : ¬ IsCptGen (pt (Int.castRingHom (ZMod 2))) := fun h => by
  have := injective_of_isCptGen _ h (a₁ := 2) (a₂ := 0) (by decide)
  exact absurd this (by decide)
end GlobalTheory.CompanionTheory.Ar.CptModel
