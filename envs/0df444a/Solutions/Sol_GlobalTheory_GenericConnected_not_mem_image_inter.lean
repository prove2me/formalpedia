-- Prove2me | solution 1 for GlobalTheory.GenericConnected.not_mem_image_inter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:50:41.076602+00:00
-- url     : https://prove2.me/submissions/83e74a91-4c96-4bc8-a6a3-cc195654029b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsIsAffineOpenDisjointImageOfIsConstructible
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GeometricallyConnectedGenericFibreOfDense
import Theorems.Thm_GlobalTheory_laurentEval_single
import Theorems.Thm_GlobalTheory_torusCoord_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.laurentEval_single
attribute [local simp] GlobalTheory.torusCoord_apply



set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
local notation "OO" p:max => (Valuation.valuationSubring (Valued.v : Valuation (PadicAlgCl p) NNReal))
local notation "cPt" p:max => (IsLocalRing.closedPoint (OO p) : Sp (OO p))
local notation "gPt" p:max => spMap (ValuationSubring.subtype (OO p))
open GlobalTheory GlobalTheory.GenericConnected
namespace GlobalTheory.GenericConnected
theorem _root_.solution {X T S : Scheme.{0}} (f : X ⟶ S) (t : T ⟶ S) (y : T)
    (h : GeometricallyConnected (f.fiberToSpecResidueField (t y)))
    (U V : (pullback f t).Opens) (hsup : U ⊔ V = ⊤) (hinf : U ⊓ V = ⊥) :
    y ∉ (pullback.snd f t '' U) ∩ (pullback.snd f t '' V) := by
  rintro ⟨⟨u, hu, hu'⟩, v, hv, hv'⟩
  have : ConnectedSpace ((pullback.snd f t).fiber y) :=
    h.geometrically_connectedSpace _ _ _
      (isPullback_fiberToSpecResidueField_of_isPullback (.of_hasPullback f t) y)
  have hc : _root_.IsPreconnected (pullback.snd f t ⁻¹' {y}) := by
    rw [← Scheme.Hom.range_fiberι, ← Set.image_univ]
    exact isPreconnected_univ.image _ (Scheme.Hom.fiberι _ _).continuous.continuousOn
  have hsup' : (U : Set ↥(pullback f t)) ∪ V = Set.univ := by
    simpa using congr(($hsup : Set ↥(pullback f t)))
  have hinf' : (U : Set ↥(pullback f t)) ∩ V = ∅ := by
    simpa using congr(($hinf : Set ↥(pullback f t)))
  obtain ⟨z, -, hz⟩ := hc U V U.2 V.2 (hsup' ▸ Set.subset_univ _) ⟨u, hu', hu⟩ ⟨v, hv', hv⟩
  rw [hinf'] at hz
  exact hz
end GlobalTheory.GenericConnected
