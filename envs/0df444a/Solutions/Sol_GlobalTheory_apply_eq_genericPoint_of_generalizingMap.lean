-- Prove2me | solution 1 for GlobalTheory.apply_eq_genericPoint_of_generalizingMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:24:07.679416+00:00
-- url     : https://prove2.me/submissions/1bd903b5-8a33-4675-b1c3-ca7c5d3c9089

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FormallyUnramifiedOfCompOfEtaleOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsIsoOfIsFiniteOfUniqueLiftOfClassicalPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_JacobsonClosedPointsToolsInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsOpensEtaleOfUniqueClassicalPoints

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
set_option backward.isDefEq.respectTransparency false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {S T : Type*} [TopologicalSpace S]
    [TopologicalSpace T] [T0Space S] [QuasiSober T] [IrreducibleSpace T] {f : S → T}
    (hf : GeneralizingMap f) {s : S} (hs : s ∈ genericPoints S) : f s = genericPoint T := by
  obtain ⟨s', hs', e⟩ := hf (genericPoint_specializes (f s))
  have h : closure {s} ⊆ closure ({s'} : Set S) := specializes_iff_closure_subset.mp hs'
  have h' := hs.2 isIrreducible_singleton.closure h
  rw [← e, (hs'.antisymm (specializes_iff_closure_subset.mpr h')).eq]
end GlobalTheory
