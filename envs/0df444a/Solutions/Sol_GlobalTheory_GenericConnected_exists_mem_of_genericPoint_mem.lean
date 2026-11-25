-- Prove2me | solution 1 for GlobalTheory.GenericConnected.exists_mem_of_genericPoint_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:50:39.419776+00:00
-- url     : https://prove2.me/submissions/8521182d-f5fc-423e-bbbf-9e05bf862034

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsIsAffineOpenDisjointImageOfIsConstructible
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GeometricallyConnectedGenericFibreOfDense
import Theorems.Thm_GlobalTheory_exists_isAffineOpen_disjoint_image_of_isConstructible_of_disjoint_dense
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
theorem _root_.solution {T S : Scheme.{0}} [IsIntegral S] [IsNoetherian S]
    (t : T ⟶ S) [LocallyOfFiniteType t] [QuasiCompact t] {C : Set T} {Sg : Set S}
    (hC : Topology.IsConstructible C) (hSg : Dense Sg) (h : genericPoint S ∈ t '' C) :
    ∃ y ∈ C, t y ∈ Sg := by
  by_contra! H
  obtain ⟨V, hV, -, hd⟩ :=
    exists_isAffineOpen_disjoint_image_of_isConstructible_of_disjoint_dense T S t C Sg hC hSg
      (Set.disjoint_left.2 (by rintro _ ⟨y, hy, rfl⟩; exact H y hy))
  exact Set.disjoint_left.1 hd h
    (((genericPoint_spec S).mem_open_set_iff V.isOpen).mpr (by simpa using hV))
end GlobalTheory.GenericConnected
