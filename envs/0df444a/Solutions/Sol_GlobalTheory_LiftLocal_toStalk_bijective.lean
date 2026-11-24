-- Prove2me | solution 1 for GlobalTheory.LiftLocal.toStalk_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:42:46.559795+00:00
-- url     : https://prove2.me/submissions/7b8532be-7c00-4f43-a4ae-395348f12446

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_SRelOneOneIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLiftLocalPointAlongAffineFlatSurjection

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LiftLocal
namespace GlobalTheory.LiftLocal
theorem _root_.solution (R : Type) [CommRing R] [IsLocalRing R] (q : PrimeSpectrum R)
    (hq : q = IsLocalRing.closedPoint R) : Function.Bijective (StructureSheaf.toStalk R q).hom := by
  subst hq
  let e := IsLocalization.atUnits R (IsLocalRing.closedPoint R).asIdeal.primeCompl
    (S := (Spec.structureSheaf R).presheaf.stalk (IsLocalRing.closedPoint R)) (fun y hy => by
      rw [IsUnit.mem_submonoid_iff]
      by_contra h
      exact hy ((IsLocalRing.mem_maximalIdeal y).mpr h))
  have : ⇑(StructureSheaf.toStalk R (IsLocalRing.closedPoint R)).hom = ⇑e :=
    funext fun r => (e.commutes r).symm
  rw [this]
  exact e.bijective
end GlobalTheory.LiftLocal
