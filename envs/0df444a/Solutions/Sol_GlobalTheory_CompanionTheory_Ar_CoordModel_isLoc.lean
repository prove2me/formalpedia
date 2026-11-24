-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.CoordModel.isLoc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:05:27.019093+00:00
-- url     : https://prove2.me/submissions/b092b887-1c80-4bad-9fa1-41026778b5a7

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
namespace GlobalTheory.CompanionTheory.Ar.CoordModel
theorem _root_.solution (p : Spec (CommRingCat.of A)) :
    letI := (toSt A p).toAlgebra
    IsLocalization.AtPrime ((Spec (CommRingCat.of A)).presheaf.stalk p) (pr A p).asIdeal :=
  StructureSheaf.IsLocalization.to_stalk A (pr A p)
end GlobalTheory.CompanionTheory.Ar.CoordModel
