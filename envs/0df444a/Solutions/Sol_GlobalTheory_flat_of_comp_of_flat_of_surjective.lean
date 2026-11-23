-- Prove2me | solution 1 for GlobalTheory.flat_of_comp_of_flat_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:03.63972+00:00
-- url     : https://prove2.me/submissions/b30b4bec-0d29-4071-8325-0491fdaa2d07

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FormallyUnramifiedOfCompOfEtaleOfSurjective
import Theorems.Thm_GlobalTheory_faithfullyFlat_stalkMap_of_flat
import Theorems.Thm_GlobalTheory_ringHom_flat_of_comp_faithfullyFlat


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
theorem _root_.solution {W X Y : Scheme.{u}} (g : W ⟶ X) (u : X ⟶ Y)
    [Flat g] [Surjective g] [Flat (g ≫ u)] : Flat u := by
  refine Flat.of_stalkMap u fun x => ?_
  obtain ⟨w, rfl⟩ := g.surjective x
  have h := Flat.stalkMap (g ≫ u) w
  rw [Scheme.Hom.stalkMap_comp] at h
  exact ringHom_flat_of_comp_faithfullyFlat (faithfullyFlat_stalkMap_of_flat g w) h
end GlobalTheory
