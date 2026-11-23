-- Prove2me | solution 1 for GlobalTheory.TorusConst.valuationRing_stalk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:35:29.169948+00:00
-- url     : https://prove2.me/submissions/8b9941a3-f2b1-418b-b634-e5047228ac3a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusToAbelianVarietyConst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.TorusConst
open Polynomial TorusToProper
namespace GlobalTheory.TorusConst
theorem _root_.solution (R : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (x : Spec (CommRingCat.of R)) : ValuationRing ((Spec (CommRingCat.of R)).presheaf.stalk x) := by
  letI : Algebra R ((Spec (CommRingCat.of R)).presheaf.stalk x) :=
    StructureSheaf.stalkAlgebra R x
  have : x.asIdeal.IsPrime := PrimeSpectrum.isPrime (R := R) x
  have : IsLocalization.AtPrime ((Spec (CommRingCat.of R)).presheaf.stalk x) x.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R x
  have : IsPrincipalIdealRing ((Spec (CommRingCat.of R)).presheaf.stalk x) := ⟨fun J => by
    rw [← IsLocalization.map_under x.asIdeal.primeCompl _ J]
    obtain ⟨a, ha⟩ := (IsPrincipalIdealRing.principal (J.under R)).principal
    rw [ha]
    exact ⟨⟨_, by rw [Ideal.submodule_span_eq, Ideal.map_span, Set.image_singleton]⟩⟩⟩
  exact ValuationRing.iff_local_bezout_domain.2 ⟨inferInstance, inferInstance⟩
end GlobalTheory.TorusConst
