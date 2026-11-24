-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.CoordModel.genPt_asIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:04:52.091599+00:00
-- url     : https://prove2.me/submissions/1f776932-611f-47a9-b8bc-913fb06627ee

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_CoordsAt
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsCoordsAtOfCoordTie

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
theorem _root_.solution : (pr A (genPt (gen A Ω))).asIdeal = ⊥ := by
  ext a
  change algebraMap A Ω a ∈ IsLocalRing.maximalIdeal Ω ↔ _
  simp
end GlobalTheory.CompanionTheory.Ar.CoordModel
