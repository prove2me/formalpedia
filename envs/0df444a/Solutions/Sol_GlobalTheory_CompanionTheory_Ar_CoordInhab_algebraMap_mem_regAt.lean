-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.CoordInhab.algebraMap_mem_regAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:49:45.334737+00:00
-- url     : https://prove2.me/submissions/86effe86-0381-479d-b690-d9f8c03ae332

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_CoordsAt
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InjectiveOfIsCptGen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_StalkClosedPointToToStalk
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CptModel_genMap_toStalk


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar
open AlgebraicGeometry CategoryTheory CptModel
open GlobalTheory.CompanionTheory.Ar.CoordInhab
variable {o K : Type} [CommRing o] [Field K] [Algebra o K]
namespace GlobalTheory.CompanionTheory.Ar.CoordInhab
theorem _root_.solution (p : Cpt (pt (algebraMap o K))) (a : o) :
    algebraMap o K a ∈ regAt (pt (algebraMap o K)) p :=
  RingHom.mem_range.2 ⟨tS p.1 a, genMap_toStalk _ p a⟩
end GlobalTheory.CompanionTheory.Ar.CoordInhab
