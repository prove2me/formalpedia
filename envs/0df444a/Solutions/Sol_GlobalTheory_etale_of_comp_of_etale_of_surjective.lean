-- Prove2me | solution 1 for GlobalTheory.etale_of_comp_of_etale_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:47:08.814951+00:00
-- url     : https://prove2.me/submissions/9d6cc5c2-1646-4316-ad00-5b0f793477c8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FormallyUnramifiedOfCompOfEtaleOfSurjective
import Theorems.Thm_GlobalTheory_flat_of_comp_of_flat_of_surjective
import Theorems.Thm_GlobalTheory_formallyUnramified_of_comp_of_etale_of_surjective

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
theorem _root_.solution {W X Y : Scheme.{u}} (g : W ⟶ X)
    (u : X ⟶ Y) [Etale g] [Surjective g] [Etale (g ≫ u)] [LocallyOfFinitePresentation u] :
    Etale u := by
  have : Flat g := (Etale.iff_flat_and_formallyUnramified.mp ‹Etale g›).1
  have : Flat (g ≫ u) := (Etale.iff_flat_and_formallyUnramified.mp ‹Etale (g ≫ u)›).1
  have := flat_of_comp_of_flat_of_surjective g u
  have := formallyUnramified_of_comp_of_etale_of_surjective g u
  exact Etale.of_formallyUnramified_of_flat u
end GlobalTheory
