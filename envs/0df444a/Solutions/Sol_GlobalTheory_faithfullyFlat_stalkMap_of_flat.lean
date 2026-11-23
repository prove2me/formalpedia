-- Prove2me | solution 1 for GlobalTheory.faithfullyFlat_stalkMap_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:25.251664+00:00
-- url     : https://prove2.me/submissions/9961f395-fe68-4bc9-8f3b-f496daeef119

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FormallyUnramifiedOfCompOfEtaleOfSurjective

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
local notation "OO" p:max => (Valuation.valuationSubring (Valued.v : Valuation (PadicAlgCl p) NNReal))
local notation "cPt" p:max => (IsLocalRing.closedPoint (OO p) : Sp (OO p))
local notation "gPt" p:max => spMap (ValuationSubring.subtype (OO p))
open GlobalTheory
universe u
namespace GlobalTheory
theorem _root_.solution {W X : Scheme.{u}} (g : W ⟶ X) [Flat g] (w : W) :
    (g.stalkMap w).hom.FaithfullyFlat := by
  have h := Flat.stalkMap g w
  algebraize [(g.stalkMap w).hom]
  have : IsLocalHom (algebraMap (X.presheaf.stalk (g w)) (W.presheaf.stalk w)) :=
    inferInstanceAs <| IsLocalHom (g.stalkMap w).hom
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom
end GlobalTheory
