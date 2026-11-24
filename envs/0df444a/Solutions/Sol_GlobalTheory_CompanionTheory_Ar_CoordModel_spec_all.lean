-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.CoordModel.spec_all
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:17:27.758876+00:00
-- url     : https://prove2.me/submissions/23105c6b-03fe-44b1-8896-c2ed7cac08fd

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_CoordsAt
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsCoordsAtOfCoordTie
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CoordModel_genPt_asIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.CoordModel
open AlgebraicGeometry CategoryTheory
variable (A : Type) [CommRing A] (Ω : Type) [Field Ω] [Algebra A Ω]
variable [IsDomain A] [IsFractionRing A Ω]
namespace GlobalTheory.CompanionTheory.Ar.CoordModel
theorem _root_.solution (q : Spec (CommRingCat.of A)) : genPt (gen A Ω) ⤳ q := by
  refine (PrimeSpectrum.le_iff_specializes (R := A) _ _).1 ?_
  change (pr A (genPt (gen A Ω))).asIdeal ≤ (pr A q).asIdeal
  rw [genPt_asIdeal]; exact bot_le
end GlobalTheory.CompanionTheory.Ar.CoordModel
