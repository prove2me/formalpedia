-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.CoordInhab.genPt_specializes
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:41.502248+00:00
-- url     : https://prove2.me/submissions/e758c3fe-fc26-4fab-a690-86eb0eb97c1f

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_CoordsAt
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InjectiveOfIsCptGen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_StalkClosedPointToToStalk

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
variable [IsFractionRing o K]
namespace GlobalTheory.CompanionTheory.Ar.CoordInhab
theorem _root_.solution (q : Spec (CommRingCat.of o)) : genPt (pt (algebraMap o K)) ⤳ q := by
  refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
  change (genPt (pt (algebraMap o K))).asIdeal ≤ _
  rw [genPt_asIdeal, (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective o K)]
  exact bot_le
end GlobalTheory.CompanionTheory.Ar.CoordInhab
