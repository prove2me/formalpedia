-- Prove2me | solution 1 for GlobalTheory.ComplexPoints.surjective_specMap_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:56:03.495393+00:00
-- url     : https://prove2.me/submissions/b8ba364b-b0d7-4ba3-b417-005944de8bc1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
universe u
open GlobalTheory GlobalTheory.ComplexPoints
variable {K : Type u} [Field K] [IsAlgClosed K]
namespace GlobalTheory.ComplexPoints
theorem _root_.solution {k L : Type u} [Field k] [Field L] (σ : k →+* L) :
    Surjective (Spec.map (CommRingCat.ofHom σ)) :=
  ⟨fun x => ⟨IsLocalRing.closedPoint L, Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩
end GlobalTheory.ComplexPoints
