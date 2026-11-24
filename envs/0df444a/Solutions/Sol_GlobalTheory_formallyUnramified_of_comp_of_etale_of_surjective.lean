-- Prove2me | solution 1 for GlobalTheory.formallyUnramified_of_comp_of_etale_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:39:43.151161+00:00
-- url     : https://prove2.me/submissions/367851b9-f8f7-4017-a554-830db359e968

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FormallyUnramifiedOfCompOfEtaleOfSurjective
import Theorems.Thm_GlobalTheory_ringHom_formallyUnramified_of_comp_faithfullyFlat
import Theorems.Thm_GlobalTheory_faithfullyFlat_stalkMap_of_flat

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
    (u : X ⟶ Y) [Etale g] [Surjective g] [FormallyUnramified (g ≫ u)] :
    FormallyUnramified u := by
  have : Flat g := (Etale.iff_flat_and_formallyUnramified.mp ‹Etale g›).1
  refine HasRingHomProperty.of_stalkMap RingHom.FormallyUnramified.ofLocalizationPrime fun x => ?_
  obtain ⟨w, rfl⟩ := g.surjective x
  have h := FormallyUnramified.stalkMap (g ≫ u) w
  rw [Scheme.Hom.stalkMap_comp] at h
  have hs : (g.stalkMap w).hom.FormallySmooth :=
    Scheme.Hom.mem_smoothLocus.mp (g.smoothLocus_eq_top.ge (Set.mem_univ w))
  exact ringHom_formallyUnramified_of_comp_faithfullyFlat (faithfullyFlat_stalkMap_of_flat g w)
    hs (FormallyUnramified.stalkMap g w) h
end GlobalTheory
